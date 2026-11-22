-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch286
-- name    : Polychromatic418967fa_Branch286
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:37:01.572279+00:00
-- url     : https://prove2.me/theorems/3f94e6ad-78d7-49e1-a873-8389d5222488
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch286_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_286 : allB 286 286 :=
  allB_succ' 2 285 286 (Eq.refl Bool.true) (allA_succ_of_accept 1 285 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  285 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 285 286)) (allB_succ' 3 284 286
  (Eq.refl Bool.true) (allA_of_3_1 3 284 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 283 286 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 283 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 283 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 283 286 (accept_3_3 2 283 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 283 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 283 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 283 286)))) (allB_succ' 5 282 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 282 286 2 2 141 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 282 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 282 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 282 286 2 1 141 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 282 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 282 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 282 286))))) (allB_succ' 6 281 286 (Eq.refl Bool.true) (allA_of_3_1 6 281 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 7 280 286 (Eq.refl Bool.true) (allA_succ_of_gcd 6 280 286 2 3 140 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 280 286 (accept_3_3 5 280 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 280 286 2 2 140 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 280 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 280 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 280 286 2 1 140 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 280 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 280 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 280 286))))))) (allB_succ' 8 279 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 279 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 279 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 279 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 279 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 279 286 (accept_3_3 5 279 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 279 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897
  4 279 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 279 286
  (Polychromatic418967fa.accept_10_3_9_6_1_94 3 279 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 279 286 (accept_3_3 2 279 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  279 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 279 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 279 286)))))))) (allB_succ' 9 278 286 (Eq.refl Bool.true) (allA_of_3_1 9 278 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 277 286 (Eq.refl Bool.true) (allA_succ_of_accept 9 277 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 277 286 (accept_3_3 8 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  277 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 277 286 (Polychromatic418967fa.accept_15_6_7_1_1_93 6 277 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 277 286 (accept_3_3 5 277 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 277 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 277 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 277 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 277 286 (accept_3_3 2 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  277 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 277 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 277 286)))))))))) (allB_succ' 11 276 286 (Eq.refl Bool.true) (allA_succ_of_gcd 10 276 286 2 5
  138 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 276 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 276 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 276 286 2 4 138 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 276 286 (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 276 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 276 286 2 3 138 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 276 286 (accept_3_3 5 276 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 276 286 2 2 138 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 276 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  276 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 276 286 2 1 138 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 276 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 276 286))))))))))) (allB_succ' 12 275 286 (Eq.refl Bool.true) (allA_of_3_1 12 275 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 274 286 (Eq.refl Bool.true) (allA_succ_of_gcd 12 274 286 2 6 137 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 274 286 (accept_3_3 11
  274 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 274 286 2 5 137 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 274 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 274 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 274 286 2 4 137 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 274 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 274 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 274 286 2 3 137 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 274 286 (accept_3_3 5 274 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 274 286 2 2 137 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 274 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3
  274 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 274 286 2 1 137 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 274 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 274 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 274 286))))))))))))) (allB_succ' 14 273 286 (Eq.refl Bool.true) (allA_succ_of_gcd 13 273 286 13 1 21 22
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 273 286
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 12 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 273 286 (accept_3_3 11 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 273 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 273 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 273 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 273 286 (accept_3_3 8 273 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 273 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 273 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 273 286 (accept_3_3 5 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  273 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 273 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 273 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 273 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 273 286 (accept_3_3 2 273 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 273 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273 286)))))))))))))) (allB_succ' 15 272 286 (Eq.refl
  Bool.true) (allA_of_3_1 15 272 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 271 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 271 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 271 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 271 286 (accept_3_3 14 271 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 271 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 271 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 271 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  271 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 271 286 (accept_3_3 11
  271 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 271 286
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 10 271 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 271 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 271 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 271 286 (accept_3_3 8 271 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 271 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 271 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 271 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 271 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 271 286 (accept_3_3 5 271 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  271 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 271 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 271 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 271 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 271 286 (accept_3_3 2 271 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 271 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 271 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 271 286)))))))))))))))) (allB_succ' 17 270 286 (Eq.refl
  Bool.true) (allA_succ_of_gcd 16 270 286 2 8 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 270 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 270 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 270 286 2 7 135 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 270 286
  (Polychromatic418967fa.accept_24_13_6_22_1_2345 13 270 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 270 286 2 6 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 270 286 (accept_3_3 11 270 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 270 286 2 5 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 270 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 270 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 270 286 2 4 135 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 270 286
  (Polychromatic418967fa.accept_19_7_4_1_1_5399 7 270 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 270 286 2 3 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 270 286 (accept_3_3 5 270 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 270 286 2 2 135 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 270 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 270 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 270 286 2 1 135 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 286
  (Polychromatic418967fa.accept_24_1_6_22_1_11014 1 270 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 286))))))))))))))))) (allB_succ' 18 269 286 (Eq.refl Bool.true) (allA_of_3_1 18 269 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 268 286 (Eq.refl Bool.true) (allA_succ_of_gcd 18 268 286 2 9 134 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 268 286
  (accept_3_3 17 268 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 268 286 2 8 134 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 268 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 268 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 268 286 2 7 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 268 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 13 268 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 268 286 2 6 134 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 268 286 (accept_3_3 11 268 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 268 286 2 5 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 268 286 (Polychromatic418967fa.accept_19_9_2_1_1_2821 9
  268 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 268 286 2 4 134 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 268 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 268 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 268 286 2 3 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 268 286 (accept_3_3 5 268 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 268 286 2 2 134 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 268 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 268 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 268 286 2 1 134 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 268 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 268 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 268 286))))))))))))))))))) (allB_succ' 20 267 286 (Eq.refl Bool.true) (allA_succ_of_accept 19 267 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 267 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 267 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 267 286 (accept_3_3 17 267 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 267 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 267 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 267 286
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 267 286 (accept_3_3 14 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 267 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 267 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 267 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 267 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 267 286 (accept_3_3 11 267 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 286 (Polychromatic418967fa.accept_9_1_6_7_1_285
  10 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 267 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 267 286 (accept_3_3 8 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  267 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 267 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 267 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 267 286 (accept_3_3 5 267 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 267 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 267 286 (accept_3_3 2 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  267 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 267 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 267 286)))))))))))))))))))) (allB_succ' 21 266 286 (Eq.refl Bool.true) (allA_of_3_1 21 266 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 265 286 (Eq.refl Bool.true) (allA_succ_of_accept 21 265 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 265 286 (accept_3_3 20 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 265 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 265 286 (Polychromatic418967fa.accept_17_1_10_14_1_1173 18 265 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 265 286 (accept_3_3 17 265 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 265 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 265
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 265 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 265 286 (accept_3_3 14 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 265 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 265 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 265 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 286 (accept_3_3 11 265 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 265 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 265 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 265 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 265 286 (accept_3_3 8 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  265 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 265 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 265 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 286 (accept_3_3 5 265 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 265 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 265 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 265 286 (accept_3_3 2 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  265 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 265 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 265 286)))))))))))))))))))))) (allB_succ' 23 264 286 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  264 286 22 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 264 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 264 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 264 286 2 10 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 264 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 19
  264 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 264 286 2 9 132 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 264 286 (accept_3_3 17
  264 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 264 286 2 8 132 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 264 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 264 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 264 286 2 7 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 264 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 264 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 264 286 2 6 132 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 264 286 11 1 24 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 264 286 2 5 132 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 264 286
  (Polychromatic418967fa.accept_18_9_12_16_1_7323 9 264 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 264 286 2 4 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 264 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 264 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264 286 2 3 132 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 264 286 (accept_3_3 5 264 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 264 286 2 2 132 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 264 286 (Polychromatic418967fa.accept_19_3_17_1_1_781 3
  264 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 264 286 2 1 132 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 264 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 264 286))))))))))))))))))))))) (allB_succ' 24 263 286 (Eq.refl Bool.true) (allA_of_3_1 24 263 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 262 286 (Eq.refl Bool.true) (allA_succ_of_gcd 24 262 286 2 12 131 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 262 286
  (accept_3_3 23 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 262 286 2 11 131 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 262 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 262 286 2 10 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 262 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 19 262 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 262 286 2 9 131 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 262 286 (accept_3_3 17 262 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 262 286 2 8 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 262 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 262 286 2 7 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 262 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 262 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 262 286 2 6 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 262 286 (accept_3_3 11 262 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 262 286 2 5 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 262 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 262
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 262 286 2 4 131 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 262 286
  (Polychromatic418967fa.accept_21_7_10_13_1_4093 7 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 262 286 2 3 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 262 286 (accept_3_3 5 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 262 286 2 2 131 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 262 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 262 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 262 286 2 1 131 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 262 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 262 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 262 286))))))))))))))))))))))))) (allB_succ' 26 261 286 (Eq.refl Bool.true) (allA_succ_of_accept 25 261 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 25 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 261 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 261 286 (accept_3_3 23 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 261 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 261 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 261 286
  (Polychromatic418967fa.accept_19_2_14_1_1_11076 21 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 261 286 (accept_3_3 20 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 261 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 261 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 261 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 261 286 (accept_3_3 17 261 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 261 286
  (Polychromatic418967fa.accept_20_16_1_6_1_6196 16 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 261 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 261 286 (accept_3_3 14 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 261 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 261 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 261 286 (Polychromatic418967fa.accept_10_2_1_6_1_634
  12 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 286 (accept_3_3 11
  261 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 261 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 261 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 261 286 (accept_3_3 8 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 261 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 261 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 286 (Polychromatic418967fa.accept_12_6_9_10_1_565
  6 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 286 (accept_3_3 5
  261 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 261 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 261 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 261 286 (accept_3_3 2 261 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 261 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 261 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261 286)))))))))))))))))))))))))) (allB_succ' 27 260 286 (Eq.refl
  Bool.true) (allA_of_3_1 27 260 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 259 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 259 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 259 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 259 286 (accept_3_3 26 259 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 259 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 259 286
  (Polychromatic418967fa.accept_17_7_4_14_1_2106 24 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 259 286 (accept_3_3 23 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 259 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 259 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 259 286 (accept_3_3 20 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 259 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 19 259 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 259 286
  (Polychromatic418967fa.accept_15_3_4_1_1_1072 18 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 259 286 (accept_3_3 17 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 259 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 259 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 259 286 (accept_3_3 14 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 259 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 259 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 259 286
  (Polychromatic418967fa.accept_15_12_4_1_1_3746 12 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 259 286 (accept_3_3 11 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 259 286 (Polychromatic418967fa.accept_20_10_19_6_1_13499 10 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 259 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 259 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 286 (accept_3_3 8 259 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 286 (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 259
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 259 286
  (Polychromatic418967fa.accept_21_6_7_13_1_7199 6 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 259 286 (accept_3_3 5 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  259 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 259 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 259 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 286 (accept_3_3 2 259 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 259 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 259 286)))))))))))))))))))))))))))) (allB_succ' 29 258
  286 (Eq.refl Bool.true) (allA_succ_of_gcd 28 258 286 2 14 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 258 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 258
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 258 286 2 13 129 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 258 286
  (Polychromatic418967fa.accept_19_6_11_1_1_6815 25 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 258 286 2 12 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 258 286 (accept_3_3 23 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 258 286 2 11 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 258 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 258 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 258 286 2 10 129 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 258 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 258 286 2 9 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 258 286 (accept_3_3 17 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 258 286 2 8 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 258 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 258 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 258 286 2 7 129 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 258 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 258 286 2 6 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 258 286 (accept_3_3 11 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 258 286 2 5 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 258 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 258 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 258 286 2 4 129 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 286
  (Polychromatic418967fa.accept_21_7_6_13_1_10406 7 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 286 2 3 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 258 286 (accept_3_3 5 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 258 286 2 2 129 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 258 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 258 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 258 286 2 1 129 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 258 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 258 286))))))))))))))))))))))))))))) (allB_succ' 30 257 286 (Eq.refl Bool.true) (allA_of_3_1 30 257 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 256 286 (Eq.refl Bool.true) (allA_succ_of_gcd 30 256 286 2 15
  128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 256
  286 (accept_3_3 29 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 256 286 2 14 128 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 256 286
  (Polychromatic418967fa.accept_17_10_1_14_1_489 27 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 256 286 2 13 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 256 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 25 256 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 256 286 2 12 128 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 256 286 (accept_3_3 23 256 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 256 286 2 11 128 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 256 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 256 286 2 10 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 256 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 256 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 256 286 2 9 128 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 256 286 (accept_3_3 17 256 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 256 286 2 8 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 256 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15
  256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 256 286 2 7 128 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 256 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 256 286 2 6 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 256 286 (accept_3_3 11 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 256 286 2 5 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 256 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 256 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 256 286 2 4 128 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 256 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 256 286 2 3 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 256 286 (accept_3_3 5 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 256 286 2 2 128 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 256 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 256 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 256 286 2 1 128 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 256 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 256 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 256 286))))))))))))))))))))))))))))))) (allB_succ' 32 255 286 (Eq.refl Bool.true) (allA_succ_of_accept 31
  255 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 255 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 255 286 (accept_3_3 29 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 255 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 255 286
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 27 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 255 286 (accept_3_3 26 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 255 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 255 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 255 286 (accept_3_3 23 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 255 286 (accept_3_3 20 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 255 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 255 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 286 (accept_3_3 17 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 255 286 (accept_3_3 14 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 255 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 255 286 (Polychromatic418967fa.accept_19_12_8_1_1_11059 12 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 286 (accept_3_3 11 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 255 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 255 286 (accept_3_3 8 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  255 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 255 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 286 (accept_3_3 5 255 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 255 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 286
  (Polychromatic418967fa.accept_24_3_15_22_1_17593 3 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 255 286 (accept_3_3 2 255 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 255 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 255 286)))))))))))))))))))))))))))))))) (allB_succ' 33 254 286 (Eq.refl
  Bool.true) (allA_of_3_1 33 254 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 253 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 253 286 11 3 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 253 286 (accept_3_3 32 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 253 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 253 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 253 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 253 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 253 286 (accept_3_3 29 253 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 253 286 (Polychromatic418967fa.accept_10_8_3_6_1_685
  28 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 253 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 253 286 (accept_3_3 26 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 253 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 253 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 253 286 (accept_3_3 23 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 253 286 11 2 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 253 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 253 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 253 286 (accept_3_3 20 253 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 253 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 253 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 253 286 (accept_3_3 17 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 253 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 253 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 286 (accept_3_3 14 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 253 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 253 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 253 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 253 286 11 1 23 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 253 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 253 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 286 (accept_3_3 8 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 286 (accept_3_3 5 253 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 253 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 286 (accept_3_3 2 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 286 (Polychromatic418967fa.accept_16_1_13_14_1_1064 1 253 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 286)))))))))))))))))))))))))))))))))) (allB_succ' 35 252 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 252 286 2 17 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 252 286 (Polychromatic418967fa.accept_27_6_9_16_1_17610 33 252 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 252 286 2 16 126 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 252 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 252 286 2 15 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 252 286 (accept_3_3 29 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 252 286 2 14 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 252 286 (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 252 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 252 286 2 13 126 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 252 286
  (Polychromatic418967fa.accept_19_6_5_1_1_2765 25 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 252 286 2 12 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 252 286 (accept_3_3 23 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 252 286 2 11 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 252 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 252 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 252 286 2 10 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 252 286
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 19 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 252 286 2 9 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 252 286 (accept_3_3 17 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 252 286 2 8 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 252 286 (Polychromatic418967fa.accept_19_15_5_1_1_5360 15 252 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 286 2 7 126 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 13 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 252 286 2 6 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 252 286 (accept_3_3 11 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 252 286 2 5 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 252 286 (Polychromatic418967fa.accept_19_9_5_1_1_2766 9 252 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 252 286 2 4 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 286
  (Polychromatic418967fa.accept_20_7_12_6_1_2164 7 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 252 286 2 3 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 252 286 (accept_3_3 5 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 252 286 2 2 126 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 252 286 (Polychromatic418967fa.accept_19_3_5_1_1_6811 3 252 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 286 2 1 126 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 252 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 286))))))))))))))))))))))))))))))))))) (allB_succ' 36 251 286 (Eq.refl Bool.true) (allA_of_3_1 36 251
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 250 286 (Eq.refl Bool.true) (allA_succ_of_gcd 36 250 286 2
  18 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 250
  286 (accept_3_3 35 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 250 286 2 17 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 250 286
  (Polychromatic418967fa.accept_38_33_22_20_1_17609 33 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 250 286 2 16 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 250 286 (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 250 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 250 286 2 15 125 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 250 286 (accept_3_3 29
  250 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 250 286 2 14 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 250 286
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 250 286 2 13 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 250 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 250 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 250 286 2 12 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 250 286 (accept_3_3 23 250 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 250 286 2 11 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 250 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 21 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 250 286 2 10 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 250 286 (Polychromatic418967fa.accept_20_19_10_6_1_14774 19 250 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 250 286 2 9 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 250 286 (accept_3_3 17 250 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 250 286 2 8 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 250 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 250 286 2 7 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 250 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 250 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 250 286 2 6 125 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 250 286 (accept_3_3 11 250 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 250 286 2 5 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 250 286
  (Polychromatic418967fa.accept_15_9_10_1_1_1062 9 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 250 286 2 4 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 250 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 250 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 250 286 2 3 125 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 250 286 (accept_3_3 5 250 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 250 286 2 2 125 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 250 286 (Polychromatic418967fa.accept_27_3_7_16_1_17608
  3 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 250 286 2 1 125 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 250 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 286))))))))))))))))))))))))))))))))))))) (allB_succ' 38 249 286 (Eq.refl Bool.true) (allA_succ_of_accept
  37 249 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 249 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 36 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 249 286 (accept_3_3 35 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 249 286 (Polychromatic418967fa.accept_19_15_2_1_1_2822 34 249
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 249 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 249 286 (accept_3_3 32 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 249 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 249 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 249 286 (accept_3_3 29 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 249 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 249 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 249 286 (accept_3_3 26 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 249 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 249 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 286 (accept_3_3 23 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 249 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 249 286 (accept_3_3 20 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 249 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 249 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 286 (accept_3_3 17 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 249 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 249 286 (accept_3_3 14 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 249 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 249 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 286 (accept_3_3 11 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 286 (accept_3_3 8 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  249 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 286 (accept_3_3 5 249 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 249 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 286 (accept_3_3 2 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  249 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 249 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 286)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 248 286 (Eq.refl Bool.true)
  (allA_of_3_1 39 248 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 247 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 247 286 13 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 247 286 (accept_3_3 38 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 247 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 247 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 247 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 247 286 (accept_3_3 35 247 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 247 286
  (Polychromatic418967fa.accept_23_11_17_10_1_16043 34 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 247 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 247 286 (accept_3_3 32 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 247 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 247 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 247 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 247 286 (accept_3_3 29 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 247 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 247 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 247 286 13 2 19 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 247 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 247 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 247 286 (accept_3_3 23 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 247 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 247 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 247 286 (accept_3_3 20
  247 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 247 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 247 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 286 (accept_3_3 17 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 247 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 247 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 286 (accept_3_3 14 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  247 286 13 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 247 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 286 (accept_3_3 11 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 247 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 286 (accept_3_3 8 247
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 286
  (Polychromatic418967fa.accept_21_7_16_13_1_2733 7 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 247 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 286 (accept_3_3 5 247 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 247 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 247 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3
  247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 286 (accept_3_3 2 247
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 286 (Polychromatic418967fa.accept_4_1_3_2_1_3
  1 247 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247
  286)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 246 286 (Eq.refl Bool.true) (allA_succ_of_gcd 40 246 286 2
  20 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 246
  286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 246 286 2 19 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 246 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 246 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 246 286 2 18 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 246 286 (accept_3_3 35 246 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 246 286 2 17 123 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 246 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 246 286 2 16 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 246 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 246 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 246 286 2 15 123 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 246 286 (accept_3_3 29 246 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 246 286 2 14 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 246 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  27 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 246 286 2 13 123 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 246 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 246 286 2 12 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 246 286 (accept_3_3 23 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 246 286 2 11 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 246 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 246 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 246 286 2 10 123 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 246 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 286 2 9 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 246 286 (accept_3_3 17 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 246 286 2 8 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 246 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 246 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 246 286 2 7 123 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 246 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 286 2 6 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 286 (accept_3_3 11 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 246 286 2 5 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 246 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 246 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 246 286 2 4 123 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 286 2 3 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 286 (accept_3_3 5 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 246 286 2 2 123 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 246 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 246 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 246 286 2 1 123 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 246 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 286))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 245 286 (Eq.refl Bool.true) (allA_of_3_1 42
  245 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 244 286 (Eq.refl Bool.true) (allA_succ_of_gcd 42 244
  286 2 21 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 244 286 (accept_3_3 41 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 244 286 2 20 122 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 244 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 244 286 2 19 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 244 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 37 244 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 244 286 2 18 122 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 244 286 (accept_3_3 35 244 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 244 286 2 17 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 244 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 244 286 2 16 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 244 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 244 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 244 286 2 15 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 244 286 (accept_3_3 29 244 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 244 286 2 14 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 244 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746
  27 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 244 286 2 13 122 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 244 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 244 286 2 12 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 244 286 (accept_3_3 23 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 244 286 2 11 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 244 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 244 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 244 286 2 10 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 244 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 244 286 2 9 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 244 286 (accept_3_3 17 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 244 286 2 8 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 244 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 244 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 244 286 2 7 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 244 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 244 286 2 6 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 244 286 (accept_3_3 11 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 244 286 2 5 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 244 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 244 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 244 286 2 4 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 244 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 244 286 2 3 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 244 286 (accept_3_3 5 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 244 286 2 2 122 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 244 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 244 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 286 2 1 122 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 1 244 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 244 286))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 243 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 243 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 243 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 243
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 243 286 (accept_3_3 41 243
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 243 286
  (Polychromatic418967fa.accept_19_2_15_1_1_3977 40 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 243 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 243 286 (accept_3_3 38 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 243 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 243 286 (accept_3_3 35
  243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 34 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 286 (accept_3_3 32 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 243 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 243 286 (Polychromatic418967fa.accept_12_6_3_10_1_224
  30 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 243 286 (accept_3_3 29
  243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 28 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 243 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 286 (accept_3_3 26 243 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 243 286
  (Polychromatic418967fa.accept_19_5_15_1_1_4041 24 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 243 286 (accept_3_3 23 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 243 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 286 (accept_3_3 20 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 243 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 243 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 243 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 243 286 (accept_3_3 17 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 243 286 (Polychromatic418967fa.accept_19_16_15_1_1_16310 16 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 243 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 286 (accept_3_3 14 243 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 243 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 243 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 286 (accept_3_3 11 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 286 (Polychromatic418967fa.accept_17_10_5_14_1_4203 10 243 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 286 (accept_3_3 8 243
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 243 286 (accept_3_3 5 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  243 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 243 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 243 286 (Polychromatic418967fa.accept_21_3_12_13_1_8816 3 243 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 286 (accept_3_3 2 243 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 243 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  286)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 242 286 (Eq.refl Bool.true) (allA_of_3_1 45 242 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 241 286 (Eq.refl Bool.true) (allA_succ_of_accept 45 241 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 241 286 (accept_3_3 44 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 241 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 241 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 241 286 (accept_3_3 41 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 241 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 241
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 241 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 241 286 (accept_3_3 38 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 241 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 241 286 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 241 286 (accept_3_3 35 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 241 286 (Polychromatic418967fa.accept_20_14_1_6_1_3352 34 241
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 241 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 241 286 (accept_3_3 32 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 241 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 241 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 241 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 241 286 (accept_3_3 29 241 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 241 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 241 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 241 286 (accept_3_3 26 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 241 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 241 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 241 286 (accept_3_3 23 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 241 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 241
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 241 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 241 286 (accept_3_3 20 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 241 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 241 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 241 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 241 286 (accept_3_3 17 241 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 241 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 241 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 241 286 (accept_3_3 14 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 241 286 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 241 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 241 286 (accept_3_3 11 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 241 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 241
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 241 286 (accept_3_3 8 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  241 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 241 286 (Polychromatic418967fa.accept_17_6_3_14_1_2078 6 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 286 (accept_3_3 5 241 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 241 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 286 (accept_3_3 2 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 286 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 241 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 286)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 240 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 240 286 2 23 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 240 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 240 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 240 286 2 22 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 240 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 240 286 2 21 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 240 286 (accept_3_3 41 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 240 286 2 20 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 240 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 240 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 240 286 2 19 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 240 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 240 286 2 18 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 240 286 (accept_3_3 35 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 240 286 2 17 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 240 286 (Polychromatic418967fa.accept_17_16_2_14_1_6715 33 240 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 240 286 2 16 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 240 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 240 286 2 15 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 240 286 (accept_3_3 29 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 240 286 2 14 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 240 286 (Polychromatic418967fa.accept_19_8_12_1_1_11084 27 240 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 286 2 13 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 240 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 240 286 2 12 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 240 286 (accept_3_3 23 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 240 286 2 11 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 240 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 240 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 240 286 2 10 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 240 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 240 286 2 9 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 240 286 (accept_3_3 17 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 240 286 2 8 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 240 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 240 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 240 286 2 7 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 240 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 286 2 6 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 240 286 (accept_3_3 11 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 240 286 2 5 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 240 286 (Polychromatic418967fa.accept_19_9_12_1_1_17607 9 240 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 286 2 4 120 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 286
  (Polychromatic418967fa.accept_19_7_12_1_1_6830 7 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 286 2 3 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 240 286 (accept_3_3 5 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 286 2 2 120 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 240 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 240 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 286 2 1 120 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 240 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 286))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 239 286 (Eq.refl Bool.true)
  (allA_of_3_1 48 239 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 238 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 238 286 2 24 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 238 286 (accept_3_3 47 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 238 286 2 23 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 238 286 (Polychromatic418967fa.accept_19_7_10_1_1_5382 45 238 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 238 286 2 22 119 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 238 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 238 286 2 21 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 238 286 (accept_3_3 41 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 238 286 2 20 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 238 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 238 286 2 19 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 238 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 238 286 2 18 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 238 286 (accept_3_3 35 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 238 286 2 17 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 238 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 238 286 2 16 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 238 286
  (Polychromatic418967fa.accept_21_10_7_13_1_10408 31 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 238 286 2 15 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 238 286 (accept_3_3 29 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 238 286 2 14 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 238 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 27 238 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 238 286 2 13 119 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 238 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 238 286 2 12 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 238 286 (accept_3_3 23 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 238 286 2 11 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 238 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 238 286 2 10 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 238 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 238 286 2 9 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 238 286 (accept_3_3 17 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 238 286 2 8 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 238 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 238 286 2 7 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 238 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 238 286 2 6 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 238 286 (accept_3_3 11 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 238 286 2 5 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 238 286 (Polychromatic418967fa.accept_19_9_10_1_1_8329 9 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 238 286 2 4 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 238 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 238 286 2 3 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 238 286 (accept_3_3 5 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 286 2 2 119 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 238 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 286 2 1 119 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 238 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 286))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 237 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 237 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 237 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 237 286 (Polychromatic418967fa.accept_19_10_9_1_1_803 48 237
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 237 286 (accept_3_3 47 237
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 237 286 (Polychromatic418967fa.accept_9_1_3_7_1_6
  46 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 237 286
  (Polychromatic418967fa.accept_17_11_16_14_1_6760 45 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 237 286 (accept_3_3 44 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 237 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 237 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 237 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 237 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 237 286 (accept_3_3 41 237 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 286 (Polychromatic418967fa.accept_9_4_3_7_1_296
  40 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 237 286 (accept_3_3 38 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 237 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 237 286 (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 286 (accept_3_3 35 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 237
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 237 286 (accept_3_3 32 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 237 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 237 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 286 (accept_3_3 29 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 237 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 237 286 (accept_3_3 26 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 237 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 237 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 237 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 286 (accept_3_3 23 237 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 286
  (Polychromatic418967fa.accept_10_1_7_6_1_91 21 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 237 286 (accept_3_3 20 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 237 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 237 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 286 (accept_3_3 17 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 286 (Polychromatic418967fa.accept_20_16_17_6_1_7799 16 237
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 237 286 (accept_3_3 14 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 237 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 237 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 286 (accept_3_3 11 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 237 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 286
  (Polychromatic418967fa.accept_20_9_17_6_1_6098 9 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 237 286 (accept_3_3 8 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  237 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 237 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 286 (accept_3_3 5 237 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 237 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 286 (accept_3_3 2 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 237 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 286)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 236 286 (Eq.refl
  Bool.true) (allA_of_3_1 51 236 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 235 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 235 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 235 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 235 286 (accept_3_3 50 235 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 235 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48
  235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 235 286 (accept_3_3 47
  235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 235 286
  (Polychromatic418967fa.accept_18_10_1_16_1_579 46 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 235 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 235 286 (accept_3_3 44 235 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 235 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 235 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 235 286 (accept_3_3 41 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 235 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 235 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 235 286 (accept_3_3 38 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 235 286
  (Polychromatic418967fa.accept_15_6_10_1_1_3675 36 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 235 286 (accept_3_3 35 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 235 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 235 286 (accept_3_3 32 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 235 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 235 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 235 286 (accept_3_3 29 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 235 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 235 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 235 286 (accept_3_3 26 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 235 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 235 286 (accept_3_3 23 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 235 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 235 286 (accept_3_3 20 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 235 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 235 286
  (Polychromatic418967fa.accept_19_18_7_1_1_2770 18 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 235 286 (accept_3_3 17 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 235 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 235 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 286 (accept_3_3 14 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 286 (accept_3_3 11 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 286 (accept_3_3 8 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 286 (Polychromatic418967fa.accept_15_7_10_1_1_1836 7 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 286 (accept_3_3 5 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 286 (accept_3_3 2 235 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 235 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235
  286)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 234 286 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 234 286 26 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 234 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 234 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 234 286 2 25 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 234 286 (Polychromatic418967fa.accept_19_11_6_1_1_2826
  49 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 234 286 2 24 117 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 234 286
  (accept_3_3 47 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 234 286 2 23 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 234 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 234 286 2 22 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 234 286 (Polychromatic418967fa.accept_19_5_6_1_1_5366 43 234 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 234 286 2 21 117 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 234 286 (accept_3_3 41 234 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 234 286 2 20 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 234 286 13 3 18 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 234 286 2 19 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 234 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 234 286 2 18 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 234 286 (accept_3_3 35 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 234 286 2 17 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 234 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 234 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 234 286 2 16 117 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 234 286 2 15 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 234 286 (accept_3_3 29 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 234 286 2 14 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 234 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 234 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 234 286 26 1 9 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 234 286 2 12 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 234 286 (accept_3_3 23 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 234 286 2 11 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 234 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 234 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 286 2 10 117 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 286
  (Polychromatic418967fa.accept_20_19_14_6_1_4726 19 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 234 286 2 9 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 234 286 (accept_3_3 17 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 286 2 8 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 234 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 234 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 286 2 7 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 234 286 13 1 18 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 234 286 2 6 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 286 (accept_3_3 11
  234 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 286 2 5 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 234 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 234 286 2 4 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 234 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 7 234 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 286 2 3 117 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 286 (accept_3_3 5 234 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 286 2 2 117 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3
  234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 286 2 1 117 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 286
  (Polychromatic418967fa.accept_17_1_13_14_1_478 1 234 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 286))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 233 286 (Eq.refl Bool.true)
  (allA_of_3_1 54 233 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 232 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 232 286 2 27 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 232 286 (accept_3_3 53 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 232 286 2 26 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 232 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 232 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 232 286 2 25 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 232 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 232 286 2 24 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 232 286 (accept_3_3 47 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 232 286 2 23 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 232 286 (Polychromatic418967fa.accept_19_7_4_1_1_5399 45 232 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 232 286 2 22 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 232 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 232 286 2 21 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 232 286 (accept_3_3 41 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 232 286 2 20 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 232 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 39 232 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 232 286 2 19 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 232 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 232 286 2 18 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 232 286 (accept_3_3 35 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 232 286 2 17 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 232 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 232 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 232 286 2 16 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 232 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 232 286 2 15 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 232 286 (accept_3_3 29 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 232 286 2 14 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 232 286 (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 232 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 232 286 2 13 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 232 286 2 12 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 232 286 (accept_3_3 23 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 232 286 2 11 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 232 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 232 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 232 286 2 10 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 232 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 232 286 2 9 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 232 286 (accept_3_3 17 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 232 286 2 8 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 232 286 (Polychromatic418967fa.accept_19_15_4_1_1_4060 15 232 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 286 2 7 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 286 2 6 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 232 286 (accept_3_3 11 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 232 286 2 5 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 232 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 232 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 286 2 4 116 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 286 2 3 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 286 (accept_3_3 5 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 286 2 2 116 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 286 (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 232 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 286 2 1 116 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 1 232 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 286))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 231 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 231 286 11 5 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 231 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 231 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 231 286 (accept_3_3 53 231 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 231 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 231
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 231 286
  (Polychromatic418967fa.accept_24_3_15_22_1_17593 51 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 231 286 (accept_3_3 50 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 231 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 231 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 231 286 (accept_3_3 47 231 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 286 (Polychromatic418967fa.accept_9_1_6_7_1_285
  46 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 231 286 11 4 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 231 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 231 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 231 286 (Polychromatic418967fa.accept_10_2_1_6_1_634
  42 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 231 286 (accept_3_3 41
  231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 231 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 286 (accept_3_3 38 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 231 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 231 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159
  36 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 286 (accept_3_3 35
  231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 286
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 34 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 231 286 11 3 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 231 286 (accept_3_3 32 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 231 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 231 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 286 (accept_3_3 29 231 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 286 (Polychromatic418967fa.accept_9_1_6_7_1_285
  28 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 286
  (Polychromatic418967fa.accept_10_7_1_6_1_673 27 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 231 286 (accept_3_3 26 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 231 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 24 231 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 286 (accept_3_3 23 231 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 231 286 11 2 21 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 286 (accept_3_3 20
  231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 231 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 286 (accept_3_3 17 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 231 286 (Polychromatic418967fa.accept_19_16_3_1_1_5389 16 231 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 286
  (Polychromatic418967fa.accept_10_5_1_6_1_672 15 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 231 286 (accept_3_3 14 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 231 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 231 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 231 286 11 1 21 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 231 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 10 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 286 (accept_3_3 8 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 231 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 231 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 286 (Polychromatic418967fa.accept_12_6_3_10_1_224
  6 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 286 (accept_3_3 5
  231 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 231 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 231 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 286 (accept_3_3 2 231 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 231 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 230 286 (Eq.refl Bool.true) (allA_of_3_1 57 230 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 58 229 286 (Eq.refl Bool.true) (allA_succ_of_accept 57 229 286 (Polychromatic418967fa.accept_6_3_1_4_1_25
  57 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 229 286 (accept_3_3 56
  229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 229 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 54 229 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 229 286 (accept_3_3 53 229 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 229 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 229 286 (accept_3_3 50 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 229 286 (Polychromatic418967fa.accept_21_7_19_13_1_7164 49 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 229 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 229 286 (accept_3_3 47 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 229 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 229 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 229 286 (accept_3_3 44 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 229 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 229 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 229 286 (accept_3_3 41 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 229 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 229 286 (accept_3_3 38 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 229 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 229 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 229 286 (accept_3_3 35 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 229 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 229 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 229 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 229 286 (accept_3_3 32 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 229 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 229 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 286 (accept_3_3 29 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 229 286 (accept_3_3 26 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 286 (accept_3_3 23 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 286 (accept_3_3 20 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 286 (accept_3_3 17 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 286 (accept_3_3 14 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 13 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 286 (accept_3_3 11 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 286 (accept_3_3 8 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 286 (accept_3_3 5 229 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 229 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 286 (accept_3_3 2 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 229 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 228 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 58 228 286 2 29 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 228 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 57 228
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 228 286 2 28 114 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 228 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 228 286 2 27 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 228 286 (accept_3_3 53 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 228 286 2 26 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 228 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 228 286 2 25 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 228 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 228 286 2 24 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 228 286 (accept_3_3 47 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 228 286 2 23 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 228 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 228 286 2 22 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 228 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 43 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 228 286 2 21 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 228 286 (accept_3_3 41 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 228 286 2 20 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 228 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 228 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 228 286 2 19 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 228 286 2 18 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 228 286 (accept_3_3 35 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 228 286 2 17 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 228 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 286 2 16 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 228 286 2 15 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 228 286 (accept_3_3 29 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 228 286 2 14 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 228 286 (Polychromatic418967fa.accept_17_10_7_14_1_4244 27 228 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 228 286 2 13 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 286
  (Polychromatic418967fa.accept_16_9_4_14_1_1878 25 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 286 2 12 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 228 286 (accept_3_3 23 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 228 286 2 11 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 228 286 (Polychromatic418967fa.accept_15_6_3_1_1_3678 21 228 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 286 2 10 114 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 286 2 9 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 228 286 (accept_3_3 17 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 228 286 2 8 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 228 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 286 2 7 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 228 286 2 6 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 228 286 (accept_3_3 11 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 228 286 2 5 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 228 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 286 2 4 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 286
  (Polychromatic418967fa.accept_16_7_4_14_1_2860 7 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 286 2 3 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 228 286 (accept_3_3 5 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 228 286 2 2 114 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 228 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 228 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 286 2 1 114 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 228 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 227 286 (Eq.refl
  Bool.true) (allA_of_3_1 60 227 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 226 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 226 286 2 30 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 226 286 (accept_3_3 59 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 226 286 2 29 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 226 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 226 286 2 28 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 226 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 55 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 226 286 2 27 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 226 286 (accept_3_3 53 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 226 286 2 26 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 226 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 226 286 2 25 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 226 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 226 286 2 24 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 226 286 (accept_3_3 47 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 226 286 2 23 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 226 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 226 286 2 22 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 226 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 226 286 2 21 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 226 286 (accept_3_3 41 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 226 286 2 20 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 226 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 226 286 2 19 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 226 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 37 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 226 286 2 18 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 226 286 (accept_3_3 35 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 226 286 2 17 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 226 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 226 286 2 16 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 226 286 2 15 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 226 286 (accept_3_3 29 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 286 2 14 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 286 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 226 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 286 2 13 113 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 286 2 12 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 286 (accept_3_3 23 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 286 2 11 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 286 2 10 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 286
  (Polychromatic418967fa.accept_17_2_5_14_1_2068 19 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 286 2 9 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 286 (accept_3_3 17 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 286 2 8 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 286 2 7 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 286 2 6 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 286 (accept_3_3 11 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 286 2 5 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 286 (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 286 2 4 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 286
  (Polychromatic418967fa.accept_21_7_16_13_1_2733 7 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 286 2 3 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 286 (accept_3_3 5 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 286 2 2 113 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 226 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 286 2 1 113 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 226 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 225 286 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 225 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 60 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 225 286 (accept_3_3 59 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 225 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 225 286 (Polychromatic418967fa.accept_27_3_9_16_1_17606 57 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 225 286 (accept_3_3 56 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 225 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 225 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 225 286 (accept_3_3 53 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 225 286 (Polychromatic418967fa.accept_16_4_1_14_1_3908 52 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 225 286 (accept_3_3 50 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 225 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 225 286 (accept_3_3 47 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 225 286 (Polychromatic418967fa.accept_19_8_16_1_1_11051 46 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 286
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 225 286 (accept_3_3 44 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 225 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 225
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 286 (accept_3_3 41 225
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 225 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 286 (accept_3_3 38 225 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 286
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 225 286 (accept_3_3 35 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 225 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 225 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 286 (accept_3_3 32 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 225 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 225 286 (accept_3_3 29 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 225 286 (Polychromatic418967fa.accept_21_7_15_13_1_5606 28 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 286 (accept_3_3 26 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 24 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 225 286 (accept_3_3 23 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 225 286 (Polychromatic418967fa.accept_19_3_16_1_1_8246 22 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 225 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 286 (accept_3_3 20 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 225 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 225 286 (accept_3_3 17 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 225 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 286 (accept_3_3 14 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 286 (accept_3_3 11 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 225 286 (Polychromatic418967fa.accept_19_10_16_1_1_8271 10 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 225 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 286 (accept_3_3 8 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 225 286 (accept_3_3 5 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  225 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 4 225 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 225 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 286 (accept_3_3 2 225 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 224 286 (Eq.refl Bool.true)
  (allA_of_3_1 63 224 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 223 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 223 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 223 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 223 286 (accept_3_3 62 223 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 223 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 223 286
  (Polychromatic418967fa.accept_29_2_20_25_1_17605 60 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 223 286 (accept_3_3 59 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 223 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 58 223 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 223 286 (accept_3_3 56 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 223 286
  (Polychromatic418967fa.accept_15_10_13_1_1_3698 55 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 223 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 223 286 (accept_3_3 53 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 223 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 223
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 223 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 223 286 (accept_3_3 50 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 223 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 223 286 (accept_3_3 47 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 223 286 (Polychromatic418967fa.accept_25_21_23_11_1_17604 46
  223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 223 286 (accept_3_3 44 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 223 286 (Polychromatic418967fa.accept_24_19_7_22_1_17603 43 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 223 286 (Polychromatic418967fa.accept_15_12_13_1_1_3695 42 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 286 (accept_3_3 41 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 286 (Polychromatic418967fa.accept_12_4_7_10_1_563
  40 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 286 (accept_3_3 38 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 286 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 286 (accept_3_3 35 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 286 (Polychromatic418967fa.accept_19_15_14_1_1_8297 34 223
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 286 (accept_3_3 32 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 286 (Polychromatic418967fa.accept_23_8_16_10_1_17602 31 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 223 286 (Polychromatic418967fa.accept_23_7_16_10_1_14382 30 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 286 (accept_3_3 29 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 286 (Polychromatic418967fa.accept_10_8_3_6_1_685
  28 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 286 (accept_3_3 26 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 286 (Polychromatic418967fa.accept_27_24_7_16_1_17588 24 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 286 (accept_3_3 23 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 286 (Polychromatic418967fa.accept_17_5_2_14_1_4270 22 223
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 286 (accept_3_3 20 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 19 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 286 (accept_3_3 17 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 223
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 286 (accept_3_3 14 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 286 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 286 (accept_3_3 11 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 10 223
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 286 (accept_3_3 8 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 7 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 286 (Polychromatic418967fa.accept_19_6_14_1_1_2752 6 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 286 (accept_3_3 5 223 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 223 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 286 (accept_3_3 2 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 222 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 222 286 2 32 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 222 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 222
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 222 286 2 31 111 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 222 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 222 286 2 30 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 222 286 (accept_3_3 59 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 222 286 2 29 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 222 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 222 286 2 28 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 222 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 222 286 2 27 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 222 286 (accept_3_3 53 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 222 286 2 26 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 222 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 222 286 2 25 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 222 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 222 286 2 24 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 222 286 (accept_3_3 47 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 222 286 2 23 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 222 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 222 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 222 286 2 22 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 222 286 2 21 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 222 286 (accept_3_3 41 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 222 286 2 20 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 222 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 222 286 2 19 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 222 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 286 2 18 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 286 (accept_3_3 35 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 222 286 2 17 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 222 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 222 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 222 286 2 16 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 286 2 15 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 286 (accept_3_3 29 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 286 2 14 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 222 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 222 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 286 2 13 111 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 286 2 12 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 286 (accept_3_3 23 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 286 2 11 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 222 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 286 2 10 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 286 2 9 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 286 (accept_3_3 17 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 286 2 8 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 286 2 7 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 286 2 6 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 286 (accept_3_3 11 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 286 2 5 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 286 2 4 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 286
  (Polychromatic418967fa.accept_19_7_13_1_1_6804 7 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 286 2 3 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 286 (accept_3_3 5 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 286 2 2 111 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 222 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 286 2 1 111 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 222 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 221 286 (Eq.refl
  Bool.true) (allA_of_3_1 66 221 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 220 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 220 286 22 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 220 286 (accept_3_3 65 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 220 286 2 32 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 220 286 (Polychromatic418967fa.accept_19_6_11_1_1_6815 63 220 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 220 286 2 31 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 220 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 220 286 2 30 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 220 286 (accept_3_3 59 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 220 286 2 29 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 220 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 220 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 220 286 2 28 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 220 286 11 5 20 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 220 286 2 27 110 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 220 286 (accept_3_3 53
  220 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 220 286 2 26 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 220 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 220 286 2 25 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 220 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 220 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 220 286 2 24 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 220 286 (accept_3_3 47 220 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 220 286 2 23 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 220 286
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 220 286 22 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 220 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 43 220 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 220 286 2 21 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 220 286 (accept_3_3 41 220 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 220 286 2 20 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 220 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 220 286 2 19 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 220 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 220 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 220 286 2 18 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 220 286 (accept_3_3 35 220 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 220 286 2 17 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 220 286 11 3 20 26 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 220 286 2 16 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 220 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 220 286 2 15 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 220 286 (accept_3_3 29 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 220 286 2 14 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 220 286 (Polychromatic418967fa.accept_19_8_11_1_1_8320 27 220 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 220 286 2 13 110 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 220 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 220 286 2 12 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 220 286 (accept_3_3 23 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 220 286 22 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 220 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 220 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 286 2 10 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 286 2 9 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 286 (accept_3_3 17 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 286 2 8 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 220 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 220 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 286 2 7 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 220 286 2 6 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 220 286 11 1 20 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 220 286 2 5 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 220 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 286 2 4 110 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 286 2 3 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 220 286 (accept_3_3 5 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 220 286 2 2 110 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 220 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 220 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 286 2 1 110 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 220 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 219 286 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 219 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 66
  219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 219 286 (accept_3_3 65
  219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 219 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 64 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 219 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 63 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 219 286 (accept_3_3 62 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 219 286 (Polychromatic418967fa.accept_7_4_2_6_1_337
  60 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 219 286 (accept_3_3 59
  219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 58 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 219 286 (accept_3_3 56 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 219 286 (Polychromatic418967fa.accept_12_6_3_10_1_224
  54 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 286 (accept_3_3 53
  219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 219 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 286 (accept_3_3 50 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 286
  (Polychromatic418967fa.accept_21_6_9_13_1_8780 48 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 219 286 (accept_3_3 47 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 219 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 286 (accept_3_3 44 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 219 286 (accept_3_3 41 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 219 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 219 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 286 (accept_3_3 38 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 219 286 (accept_3_3 35 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 219 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 286 (accept_3_3 32 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 219 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 286 (accept_3_3 29 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 286 (Polychromatic418967fa.accept_20_7_19_6_1_4742 27 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 286 (accept_3_3 26 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 219 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 286 (accept_3_3 23 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 286 (accept_3_3 20 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 286 (accept_3_3 17 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 286 (Polychromatic418967fa.accept_17_16_15_14_1_6747 16 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 286 (accept_3_3 14 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 219 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 286
  (Polychromatic418967fa.accept_17_12_15_14_1_6746 12 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 286 (accept_3_3 11 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 219 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 286 (accept_3_3 8 219 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 219 286 (accept_3_3 5 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  219 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 219 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 219 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 286 (accept_3_3 2 219 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 218 286 (Eq.refl Bool.true)
  (allA_of_3_1 69 218 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 217 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 217 286 (accept_3_3 68 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 217 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 217 286 (accept_3_3 65
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 217 286
  (Polychromatic418967fa.accept_12_4_1_10_1_221 64 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 217 286 (accept_3_3 62 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 217 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 61 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 217 286 (Polychromatic418967fa.accept_9_6_1_7_1_577
  60 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 217 286 (accept_3_3 59
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 217 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 217 286 (accept_3_3 56 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 217 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075
  54 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 217 286 (accept_3_3 53
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 217 286
  (Polychromatic418967fa.accept_12_4_1_10_1_221 52 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 217 286 (accept_3_3 50 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 217 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 217 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 48
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 286 (accept_3_3 47
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 286
  (Polychromatic418967fa.accept_18_10_1_16_1_579 46 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 217 286 (accept_3_3 44 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 217 286 (Polychromatic418967fa.accept_9_6_1_7_1_577
  42 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 286 (accept_3_3 41
  217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 40 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 286 (accept_3_3 38 217 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 217 286 (Polychromatic418967fa.accept_16_5_9_14_1_5051 37 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 217 286
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 217 286 (accept_3_3 35 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 217 286 (Polychromatic418967fa.accept_19_15_8_1_1_6794 34 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 286 (accept_3_3 32 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 286 (accept_3_3 29 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 286 (accept_3_3 26 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 217 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 286 (accept_3_3 23 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 286 (accept_3_3 20 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 286
  (Polychromatic418967fa.accept_17_1_13_14_1_478 18 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 286 (accept_3_3 17 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 286 (accept_3_3 14 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 286 (accept_3_3 11 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 286 (accept_3_3 8 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 286 (accept_3_3 5 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 286 (accept_3_3 2 217 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 1 217 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 216 286 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 216 286 2 35 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 216 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 69 216 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 216 286 2 34 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 216 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 67 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 216 286 2 33 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 216 286 (accept_3_3 65 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 216 286 2 32 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 216 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 63 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 216 286 2 31 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 216 286
  (Polychromatic418967fa.accept_19_4_7_1_1_1683 61 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 216 286 2 30 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 216 286 (accept_3_3 59 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 216 286 2 29 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 216 286 (Polychromatic418967fa.accept_20_17_16_6_1_14775 57 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 216 286 2 28 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 216 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 55 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 216 286 2 27 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 216 286 (accept_3_3 53 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 216 286 2 26 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 216 286 (Polychromatic418967fa.accept_19_13_7_1_1_5379 51 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 216 286 2 25 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 216 286
  (Polychromatic418967fa.accept_17_15_12_14_1_2087 49 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 216 286 2 24 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 216 286 (accept_3_3 47 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 216 286 2 23 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 216 286 (Polychromatic418967fa.accept_17_11_12_14_1_5431 45 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 216 286 2 22 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 286
  (Polychromatic418967fa.accept_17_9_12_14_1_5423 43 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 216 286 2 21 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 216 286 (accept_3_3 41 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 216 286 2 20 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 216 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 39 216 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 216 286 2 19 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 37 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 286 2 18 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 216 286 (accept_3_3 35 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 216 286 2 17 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 216 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 33 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 216 286 2 16 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 286
  (Polychromatic418967fa.accept_19_12_7_1_1_5400 31 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 286 2 15 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 216 286 (accept_3_3 29 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 216 286 2 14 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 216 286 (Polychromatic418967fa.accept_19_8_7_1_1_6801 27 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 286 2 13 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 286 2 12 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 216 286 (accept_3_3 23 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 216 286 2 11 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 216 286 (Polychromatic418967fa.accept_19_2_7_1_1_2808 21 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 286 2 10 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 286
  (Polychromatic418967fa.accept_21_19_6_13_1_8800 19 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 216 286 2 9 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 216 286 (accept_3_3 17 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 216 286 2 8 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 216 286 (Polychromatic418967fa.accept_17_15_12_14_1_2087 15 216 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 286 2 7 108 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 286
  (Polychromatic418967fa.accept_19_13_7_1_1_5379 13 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 286 2 6 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 216 286 (accept_3_3 11 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 216 286 2 5 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 216 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 216 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 286 2 4 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 286 2 3 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 216 286 (accept_3_3 5 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 216 286 2 2 108 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 216 286 (Polychromatic418967fa.accept_15_3_6_1_1_1834 3 216 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 286 2 1 108 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 286
  (Polychromatic418967fa.accept_20_1_16_6_1_4715 1 216 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 215 286
  (Eq.refl Bool.true) (allA_of_3_1 72 215 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 214 286 (Eq.refl
  Bool.true) (allA_succ_of_gcd 72 214 286 2 36 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 214 286 (accept_3_3 71 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 214 286 2 35 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 214 286 (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 214 286 2 34 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 214 286
  (Polychromatic418967fa.accept_33_1_16_22_1_17601 67 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 214 286 2 33 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 214 286 (accept_3_3 65 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 214 286 2 32 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 214 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 214 286 2 31 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 214 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 214 286 2 30 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 214 286 (accept_3_3 59 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 214 286 2 29 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 214 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 57 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 214 286 2 28 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 214 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 55 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 214 286 2 27 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 214 286 (accept_3_3 53 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 214 286 2 26 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 214 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 214 286 2 25 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 214 286
  (Polychromatic418967fa.accept_20_9_14_6_1_320 49 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 214 286 2 24 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 286 (accept_3_3 47 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 214 286 2 23 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 214 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 214 286 2 22 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 214 286
  (Polychromatic418967fa.accept_21_1_4_13_1_7128 43 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 214 286 2 21 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 214 286 (accept_3_3 41 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 286 2 20 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 286 (Polychromatic418967fa.accept_17_5_10_14_1_2083 39 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 286 2 19 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 286 2 18 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 286 (accept_3_3 35 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 286 2 17 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 286 2 16 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 286 2 15 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 286 (accept_3_3 29 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 286 2 14 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 286 2 13 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 286 2 12 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 286 (accept_3_3 23 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 286 2 11 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 286 (Polychromatic418967fa.accept_20_1_14_6_1_4725 21 214 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 286 2 10 107 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 286 2 9 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 286 (accept_3_3 17 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 286 2 8 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 286 2 7 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 286
  (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 214 286 2 6 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 214 286 (accept_3_3 11 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 286 2 5 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 286 2 4 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 286
  (Polychromatic418967fa.accept_17_7_10_14_1_8022 7 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 286 2 3 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 286 (accept_3_3 5 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 286 2 2 107 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 214 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 286 2 1 107 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 286
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 214 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 213 286
  (Eq.refl Bool.true) (allA_succ_of_accept 73 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 213 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 213 286 (accept_3_3 71 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 213 286 (Polychromatic418967fa.accept_31_8_27_7_1_17600 70 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 213 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 69 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 213 286 (accept_3_3 68 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 213 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 213 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 66 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 213 286 (accept_3_3 65 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 213 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 213 286 (accept_3_3 62 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 213 286 (accept_3_3 59 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 213 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 213 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 286 (accept_3_3 56 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 213 286 (accept_3_3 53 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 213 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 286 (accept_3_3 50 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 213 286 (accept_3_3 47 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 213 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 213 286 (Polychromatic418967fa.accept_18_9_15_16_1_8759 45 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 286 (accept_3_3 44 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 213 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 213 286 (accept_3_3 41 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 213 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 286 (accept_3_3 38 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 213 286 (accept_3_3 35 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 213 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 213 286 (Polychromatic418967fa.accept_21_12_3_13_1_7145 33 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 286 (accept_3_3 32 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 213 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 213 286 (accept_3_3 29 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 213 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 286 (accept_3_3 26 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 286
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 213 286 (accept_3_3 23 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 213 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 213 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 286 (accept_3_3 20 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 213 286 (accept_3_3 17 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 213 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 286 (accept_3_3 14 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 286 (accept_3_3 11 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 286 (accept_3_3 8 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 286 (accept_3_3 5 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 213 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 286 (accept_3_3 2 213 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 212 286 (Eq.refl
  Bool.true) (allA_of_3_1 75 212 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 211 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 211 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 211 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 211 286 (accept_3_3 74 211 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 211 286 (Polychromatic418967fa.accept_7_2_1_6_1_173
  72 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 211 286 (accept_3_3 71
  211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 211 286
  (Polychromatic418967fa.accept_19_13_2_1_1_4054 70 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 211 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 211 286 (accept_3_3 68 211 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 211 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 67 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 211 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 211 286 (accept_3_3 65 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 211 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 211 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 211 286 (accept_3_3 62 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 211 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 211 286 (accept_3_3 59 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 211 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 211 286 (accept_3_3 56 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 211 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 211 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 211 286 (accept_3_3 53 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 211 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 211 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 286 (accept_3_3 50 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 286 (accept_3_3 47 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 286 (accept_3_3 44 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 286 (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 211 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 286 (accept_3_3 41 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 286 (accept_3_3 38 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 286
  (Polychromatic418967fa.accept_20_16_11_6_1_10684 36 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 211 286 (accept_3_3 35 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 211 286 (Polychromatic418967fa.accept_19_15_2_1_1_2822 34 211 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 211 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 286 (accept_3_3 32 211 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 286
  (Polychromatic418967fa.accept_19_12_2_1_1_12338 31 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 286 (accept_3_3 29 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 286 (accept_3_3 26 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 286 (accept_3_3 23 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 22 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 286 (accept_3_3 20 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 286 (Polychromatic418967fa.accept_19_18_2_1_1_5375 18 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 286 (accept_3_3 17 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 211 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 286 (accept_3_3 14 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 286 (accept_3_3 11 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 286 (accept_3_3 8 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 286 (Polychromatic418967fa.accept_10_7_1_6_1_673 7 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 286 (accept_3_3 5 211 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 211 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 286 (accept_3_3 2 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 210 286 (Eq.refl Bool.true) (allA_succ_of_gcd 76 210 286 2 38 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 210 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  75 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 210 286 2 37 105 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 210 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 210 286 2 36 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 210 286 (accept_3_3 71 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 210 286 2 35 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 210 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 210 286 2 34 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 210 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 210 286 2 33 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 210 286 (accept_3_3 65 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 210 286 2 32 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 210 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 210 286 2 31 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 210 286
  (Polychromatic418967fa.accept_27_7_21_16_1_17599 61 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 210 286 2 30 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 210 286 (accept_3_3 59 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 210 286 2 29 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 210 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 57 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 210 286 2 28 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 210 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 286 2 27 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 286 (accept_3_3 53 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 210 286 2 26 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 210 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 210 286 2 25 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 210 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 286 2 24 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 286 (accept_3_3 47 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 210 286 2 23 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 210 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 210 286 2 22 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 286
  (Polychromatic418967fa.accept_25_18_10_11_1_17533 43 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 210 286 2 21 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 210 286 (accept_3_3 41 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 210 286 2 20 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 210 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 210 286 2 19 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 286 2 18 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 286 (accept_3_3 35 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 210 286 2 17 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 210 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 210 286 2 16 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 286 2 15 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 286 (accept_3_3 29 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 286 2 14 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 210 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 286 2 13 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 286
  (Polychromatic418967fa.accept_17_8_6_14_1_6718 25 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 286 2 12 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 286 (accept_3_3 23 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 286 2 11 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 210 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 210 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 286 2 10 105 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 286 2 9 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 286 (accept_3_3 17 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 286 2 8 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 210 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 286 2 7 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 286 2 6 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 286 (accept_3_3 11 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 286 2 5 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 286 2 4 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 286
  (Polychromatic418967fa.accept_17_7_6_14_1_6737 7 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 286 2 3 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 286 (accept_3_3 5 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 286 2 2 105 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 210 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 286 2 1 105 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 209 286
  (Eq.refl Bool.true) (allA_of_3_1 78 209 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 208 286 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 208 286 26 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 208 286 (accept_3_3 77 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 208 286 2 38 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 208 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 208 286 2 37 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 208 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 73 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 208 286 2 36 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 208 286 (accept_3_3 71 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 208 286 2 35 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 208 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 208 286 2 34 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 208 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 67 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 208 286 2 33 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 208 286 13 5 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 208 286 2 32 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 208 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 208 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 208 286 2 31 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 208 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 208 286 2 30 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 208 286 (accept_3_3 59 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 208 286 2 29 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 208 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 208 286 2 28 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 208 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 208 286 2 27 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 208 286 (accept_3_3 53 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 208 286 26 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 208 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 208 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 208 286 2 25 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 208 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 49
  208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 208 286 2 24 104 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 208 286
  (accept_3_3 47 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 208 286 2 23 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 208 286
  (Polychromatic418967fa.accept_19_7_18_1_1_1662 45 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 208 286 2 22 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 208 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 208 286 2 21 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 208 286 (accept_3_3 41 208 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 208 286 2 20 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 208 286 13 3 16 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 208 286 2 19 104 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 208 286 2 18 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 208 286 (accept_3_3 35 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 208 286 2 17 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 208 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 208 286 2 16 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 208 286 2 15 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 208 286 (accept_3_3 29 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 208 286 2 14 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 208 286 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 208 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 208 286 26 1 8 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 208 286 2 12 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 208 286 (accept_3_3 23 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 208 286 2 11 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 208 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 286 2 10 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 208 286 2 9 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 208 286 (accept_3_3 17 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 286 2 8 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 286 2 7 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 13 208 286 13 1 16 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 208 286 2 6 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 286 (accept_3_3 11
  208 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 286 2 5 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 286
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 286 2 4 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 208 286 (Polychromatic418967fa.accept_12_7_4_10_1_572 7 208 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 286 2 3 104 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 286 (accept_3_3 5 208 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 286 2 2 104 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3
  208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 286 2 1 104 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 208 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 207
  286 (Eq.refl Bool.true) (allA_succ_of_accept 79 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 207 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 78 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 207 286 (accept_3_3 77 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 207 286 (Polychromatic418967fa.accept_20_16_7_6_1_7815 76 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 207 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 207 286 (accept_3_3 74 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 207 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 207 286 (accept_3_3 71 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 207 286 (Polychromatic418967fa.accept_17_2_3_14_1_8043 70 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 207 286 (accept_3_3 68 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 207 286 (accept_3_3 65 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 207 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 64 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 207 286 (Polychromatic418967fa.accept_10_3_7_6_1_659 63 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 207 286 (accept_3_3 62 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 207 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 286
  (Polychromatic418967fa.accept_19_3_17_1_1_781 60 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 207 286 (accept_3_3 59 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 207 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 286 (accept_3_3 56 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 207 286 (accept_3_3 53 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 207 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 207 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 286 (accept_3_3 50 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 286
  (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 207 286 (accept_3_3 47 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 286 (Polychromatic418967fa.accept_21_4_18_13_1_10435 46 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 286 (accept_3_3 44
  207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 207 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 42 207 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 286 (accept_3_3 41 207 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 207 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 286
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 286 (accept_3_3 38 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 207 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 286 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 207
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 286 (accept_3_3 35 207
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 286
  (Polychromatic418967fa.accept_15_4_12_1_1_1081 34 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 207 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 286 (accept_3_3 32 207 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 286 (Polychromatic418967fa.accept_7_2_4_6_1_166
  30 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 286 (accept_3_3 29
  207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 28 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 286 (Polychromatic418967fa.accept_21_6_18_13_1_8767 27 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 286 (accept_3_3 26 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 207 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 207 286 (accept_3_3 23 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 207 286 (Polychromatic418967fa.accept_19_3_17_1_1_781 22 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 286 (accept_3_3 20 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 207 286 (accept_3_3 17 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 207 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 286 (Polychromatic418967fa.accept_17_15_3_14_1_4230 15 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 286 (accept_3_3 14 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 207 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 286 (accept_3_3 11 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 286 (accept_3_3 8 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 286 (accept_3_3 5 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 286 (Polychromatic418967fa.accept_15_4_12_1_1_1081 4 207 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 286 (accept_3_3 2 207 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 206 286 (Eq.refl
  Bool.true) (allA_of_3_1 81 206 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 205 286 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 205 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 205 286 (accept_3_3 80 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 205 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 78
  205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 205 286 (accept_3_3 77
  205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 205 286
  (Polychromatic418967fa.accept_12_4_1_10_1_221 76 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 205 286 (accept_3_3 74 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 205 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 205 286
  (Polychromatic418967fa.accept_17_4_1_14_1_4296 72 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 205 286 (accept_3_3 71 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 205 286 (Polychromatic418967fa.accept_20_10_5_6_1_12032 70 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 205 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 205 286 (accept_3_3 68 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 205 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 205 286 (accept_3_3 65 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 205 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 205 286 (accept_3_3 62 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 205 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 61 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 205 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 205 286 (accept_3_3 59 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 205 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 58 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 205 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 205 286 (accept_3_3 56 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 205 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 205 286 (accept_3_3 53 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 205 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 205 286 (accept_3_3 50 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 205 286 (Polychromatic418967fa.accept_10_9_5_6_1_691 49 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 286
  (Polychromatic418967fa.accept_21_6_16_13_1_4100 48 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 205 286 (accept_3_3 47 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 205 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 205 286 (accept_3_3 44 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 286
  (Polychromatic418967fa.accept_16_10_13_14_1_5042 42 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 205 286 (accept_3_3 41 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 205 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 286 (accept_3_3 38 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 286
  (Polychromatic418967fa.accept_15_7_10_1_1_1836 37 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 205 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 286 (accept_3_3 35 205 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 205 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 34 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 286 (accept_3_3 32 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 286 (Polychromatic418967fa.accept_17_13_1_14_1_1149 30 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 286 (accept_3_3 29 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 205
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 286 (accept_3_3 26 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 205 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 205 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 286 (accept_3_3 23 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 286 (accept_3_3 20 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 286 (accept_3_3 17 205 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 286 (accept_3_3 14 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 286 (Polychromatic418967fa.accept_15_13_10_1_1_1862 13 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 286 (Polychromatic418967fa.accept_20_12_5_6_1_6205 12 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 286 (accept_3_3 11 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 286 (accept_3_3 8 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 6 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 286 (accept_3_3 5 205 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 205 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 286 (accept_3_3 2 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 204 286 (Eq.refl Bool.true) (allA_succ_of_gcd 82 204 286 2 41 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 204 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 204 286 2 40 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 204 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 204 286 2 39 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 204 286 (accept_3_3 77 204 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 204 286 2 38 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 204 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75
  204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 204 286 2 37 102 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 204 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 73 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 204 286 2 36 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 204 286 (accept_3_3 71 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 204 286 2 35 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 204 286 (Polychromatic418967fa.accept_18_15_6_16_1_4730 69 204 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 204 286 2 34 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 204 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 204 286 2 33 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 286 (accept_3_3 65 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 204 286 2 32 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 204 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 204 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 204 286 2 31 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 286 2 30 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 286 (accept_3_3 59 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 204 286 2 29 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 204 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 204 286 2 28 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 286 2 27 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 286 (accept_3_3 53 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 204 286 2 26 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 204 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 204 286 2 25 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 286 2 24 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 286 (accept_3_3 47 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 286 2 23 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 204 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 45 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 204 286 2 22 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 286
  (Polychromatic418967fa.accept_25_18_4_11_1_17577 43 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 204 286 2 21 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 204 286 (accept_3_3 41 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 204 286 2 20 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 204 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 204 286 2 19 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 286 2 18 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 204 286 (accept_3_3 35 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 204 286 2 17 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 204 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 286 2 16 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 286 2 15 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 204 286 (accept_3_3 29 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 286 2 14 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 204 286 (Polychromatic418967fa.accept_21_6_15_13_1_13252 27 204 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 286 2 13 102 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 286
  (Polychromatic418967fa.accept_10_5_4_6_1_319 25 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 286 2 12 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 204 286 (accept_3_3 23 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 204 286 2 11 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 204 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 286 2 10 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 286 2 9 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 204 286 (accept_3_3 17 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 204 286 2 8 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 204 286 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 286 2 7 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 286 2 6 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 286 (accept_3_3 11 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 286 2 5 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 286 2 4 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 286 2 3 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 286 (accept_3_3 5 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 286 2 2 102 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 204 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 204 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 286 2 1 102 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84
  203 286 (Eq.refl Bool.true) (allA_of_3_1 84 203 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 202 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 202 286 2 42 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 202 286 (accept_3_3 83 202 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 82 202 286 2 41 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 202 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 81 202 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 202 286 2 40 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 202 286
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 79 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 202 286 2 39 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 202 286 (accept_3_3 77 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 202 286 2 38 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 202 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 202 286 2 37 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 202 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 202 286 2 36 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 202 286 (accept_3_3 71 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 202 286 2 35 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 202 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 202 286 2 34 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 202 286
  (Polychromatic418967fa.accept_17_16_15_14_1_6747 67 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 202 286 2 33 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 202 286 (accept_3_3 65 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 202 286 2 32 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 202 286 (Polychromatic418967fa.accept_16_15_10_14_1_2872 63 202 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 202 286 2 31 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 202 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 202 286 2 30 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 202 286 (accept_3_3 59 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 202 286 2 29 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 202 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 202 286 2 28 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 202 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 202 286 2 27 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 202 286 (accept_3_3 53 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 202 286 2 26 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 202 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 286 2 25 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 286
  (Polychromatic418967fa.accept_19_11_12_1_1_11049 49 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 202 286 2 24 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 202 286 (accept_3_3 47 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 286 2 23 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 286 (Polychromatic418967fa.accept_16_13_10_14_1_2871 45 202 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 286 2 22 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 286
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 43 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 286 2 21 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 286 (accept_3_3 41 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 286 2 20 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 286 2 19 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 286 2 18 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 286 (accept_3_3 35 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 286 2 17 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 286 2 16 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 31 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 286 2 15 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 286 (accept_3_3 29 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 286 2 14 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 286 (Polychromatic418967fa.accept_19_8_12_1_1_11084 27 202 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 286 2 13 101 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 286
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 25 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 286 2 12 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 286 (accept_3_3 23 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 286 2 11 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 286 2 10 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 286 2 9 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 286 (accept_3_3 17 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 286 2 8 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 286 2 7 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 286
  (Polychromatic418967fa.accept_16_13_10_14_1_2871 13 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 202 286 2 6 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 202 286 (accept_3_3 11 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 286 2 5 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 9 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 286 2 4 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 286
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 286 2 3 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 286 (accept_3_3 5 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 286 2 2 101 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 202 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 286 2 1 101 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 202 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  201 286 (Eq.refl Bool.true) (allA_succ_of_accept 85 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 201 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 201 286
  (Polychromatic418967fa.accept_15_9_6_1_1_493 84 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 201 286 (accept_3_3 83 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 201 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 201 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 201 286 (accept_3_3 80 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 201 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 201 286 (accept_3_3 77 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 201 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 201 286 (accept_3_3 74 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 201 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 72 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 201 286 (accept_3_3 71 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 201 286 (Polychromatic418967fa.accept_15_10_6_1_1_3707 70 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 201 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 286 (accept_3_3 68 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 66 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 201 286 (accept_3_3 65 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 201 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 286 (accept_3_3 62 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 201 286 (accept_3_3 59 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 201 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 201 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 286 (accept_3_3 56 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 201 286 (accept_3_3 53 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 201 286 (Polychromatic418967fa.accept_10_2_1_6_1_634 52 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 286 (accept_3_3 50 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 286
  (Polychromatic418967fa.accept_15_3_6_1_1_1834 48 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 201 286 (accept_3_3 47 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 201 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 201 286 (Polychromatic418967fa.accept_10_5_1_6_1_672 45 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 286 (accept_3_3 44 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 201 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 201 286 (accept_3_3 41 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 201 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 286 (accept_3_3 38 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 201 286 (accept_3_3 35 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 201 286 (Polychromatic418967fa.accept_19_15_11_1_1_12437 34 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 286 (accept_3_3 32 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 201 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 286 (accept_3_3 29 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 201 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 286 (accept_3_3 26 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 286 (accept_3_3 23 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 201 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 286 (Polychromatic418967fa.accept_16_5_9_14_1_5051 21 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 286 (accept_3_3 20 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 201 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 201 286 (accept_3_3 17 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 201 286 (Polychromatic418967fa.accept_20_16_1_6_1_6196 16 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 286 (accept_3_3 14 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 286
  (Polychromatic418967fa.accept_10_2_1_6_1_634 12 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 286 (accept_3_3 11 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 201 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 286 (Polychromatic418967fa.accept_15_9_6_1_1_493 9 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 286 (accept_3_3 8 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 286 (accept_3_3 5 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 201 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 286 (accept_3_3 2 201 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 200 286
  (Eq.refl Bool.true) (allA_of_3_1 87 200 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 199 286 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 199 286 (accept_3_3 86 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 199 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 199 286 (accept_3_3 83 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 199 286 (Polychromatic418967fa.accept_18_10_1_16_1_579 82 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 199 286 (accept_3_3 80 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 199 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 199 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 199 286 (accept_3_3 77 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 199 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 199 286 (accept_3_3 74 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 199 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 199 286 (accept_3_3 71 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 199 286 (Polychromatic418967fa.accept_20_10_19_6_1_13499 70 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 199 286 (accept_3_3 68 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 199 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 199 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 199 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 199 286 (accept_3_3 65 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 199 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 199 286 (accept_3_3 62 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 286 (accept_3_3 59 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 286 (accept_3_3 56 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 286 (Polychromatic418967fa.accept_10_5_9_6_1_697 55 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 286
  (Polychromatic418967fa.accept_20_14_19_6_1_12003 54 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 199 286 (accept_3_3 53 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 199 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 199 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 199 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 286 (accept_3_3 50 199 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 286 (accept_3_3 47 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 286 (accept_3_3 44 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 43 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 286 (accept_3_3 41 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 286 (accept_3_3 38 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 286
  (Polychromatic418967fa.accept_16_4_7_14_1_3897 36 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 286 (accept_3_3 35 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 286 (Polychromatic418967fa.accept_20_14_19_6_1_12003 34 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 286 (accept_3_3 32 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 286 (accept_3_3 29 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 286 (accept_3_3 26 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 286 (accept_3_3 23 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 286 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 286 (accept_3_3 20 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 286 (Polychromatic418967fa.accept_23_19_15_10_1_12865 19 199 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 286 (accept_3_3 17 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 286 (accept_3_3 14 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 286
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 286 (accept_3_3 11 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 286 (Polychromatic418967fa.accept_14_10_3_6_1_2728 10 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 286 (accept_3_3 8 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 286 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 286
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 286 (accept_3_3 5 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 199 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 286 (accept_3_3 2 199 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 198 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 198 286 22 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 198 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 198 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 198 286 2 43 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 198 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 198 286 2 42 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 198 286 (accept_3_3 83 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 198 286 2 41 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 198 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 198 286 2 40 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 198 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 79 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 198 286 2 39 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 198 286 11 7 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 198 286 2 38 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 198 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 198
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 198 286 2 37 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 198 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 198 286 2 36 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 198 286 (accept_3_3 71 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 198 286 2 35 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 198 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 198 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 198 286 2 34 99 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 198 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 286 22 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 198 286 (accept_3_3 65 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64
  198 286 2 32 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 198 286 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 198 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 198 286 2 31 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 198 286
  (Polychromatic418967fa.accept_24_13_6_22_1_2345 61 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 198 286 2 30 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 198 286 (accept_3_3 59 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 198 286 2 29 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 198 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 198 286 2 28 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 198 286 11 5 18 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 198 286 2 27 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 198 286 (accept_3_3 53
  198 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 286 2 26 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 51 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 286 2 25 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 49 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 198 286 2 24 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 198 286 (accept_3_3 47 198 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 286 2 23 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45
  198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 198 286 22 2 9 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 286 2 21 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 286 (accept_3_3 41 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 198 286 2 20 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 198 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 198 286 2 19 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 286
  (Polychromatic418967fa.accept_17_3_11_14_1_2071 37 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 198 286 2 18 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 198 286 (accept_3_3 35 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 198 286 2 17 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 198 286 11 3 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 198 286 2 16 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 198 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 286 2 15 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 286 (accept_3_3 29
  198 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 286 2 14 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 286
  (Polychromatic418967fa.accept_12_3_6_10_1_576 27 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 286 2 13 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 286 2 12 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 286 (accept_3_3 23 198 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 286 22 1 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085
  21 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 286 2 10 99 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 286
  (Polychromatic418967fa.accept_15_4_3_1_1_487 19 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 286 2 9 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 286 (accept_3_3 17 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 286 2 8 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 198 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 286 2 7 99 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 286
  (Polychromatic418967fa.accept_10_3_8_6_1_326 13 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 286 2 6 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 11 198 286 11 1 18 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 198 286 2 5 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 198 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 286 2 4 99 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 286
  (Polychromatic418967fa.accept_19_7_8_1_1_4028 7 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 286 2 3 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 286 (accept_3_3 5 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  286 2 2 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 198 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 286 2 1 99 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 198 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 197 286
  (Eq.refl Bool.true) (allA_of_3_1 90 197 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 196 286 (Eq.refl
  Bool.true) (allA_succ_of_gcd 90 196 286 2 45 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 196 286 (accept_3_3 89 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 196 286 2 44 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 196 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 87 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 196 286 2 43 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 85 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 196 286 2 42 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 196 286 (accept_3_3 83 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 196 286 2 41 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 196 286 (Polychromatic418967fa.accept_16_1_4_14_1_1896 81 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 196 286 2 40 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 196 286 2 39 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 196 286 (accept_3_3 77 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 196 286 2 38 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 196 286 (Polychromatic418967fa.accept_19_18_6_1_1_12398 75 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 196 286 2 37 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 196 286 2 36 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 196 286 (accept_3_3 71 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 196 286 2 35 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 196 286 (Polychromatic418967fa.accept_21_6_7_13_1_7199 69 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 196 286 2 34 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 67 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 196 286 2 33 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 196 286 (accept_3_3 65 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 196 286 2 32 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 196 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 196 286 2 31 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 196 286 2 30 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 196 286 (accept_3_3 59 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 196 286 2 29 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 196 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 57 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 196 286 2 28 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 55 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 196 286 2 27 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 196 286 (accept_3_3 53 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 196 286 2 26 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 196 286 (Polychromatic418967fa.accept_20_11_16_6_1_6121 51 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 196 286 2 25 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 196 286 2 24 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 196 286 (accept_3_3 47 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 196 286 2 23 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 196 286 (Polychromatic418967fa.accept_19_7_6_1_1_796 45 196 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 196 286 2 22 98 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 196 286 2 21 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 196 286 (accept_3_3 41 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 196 286 2 20 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 196 286 (Polychromatic418967fa.accept_16_7_4_14_1_2860 39 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 196 286 2 19 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 196 286 2 18 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 196 286 (accept_3_3 35 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 196 286 2 17 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 196 286 (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 286 2 16 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 31 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 196 286 2 15 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 196 286 (accept_3_3 29 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 196 286 2 14 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 196 286 (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 286 2 13 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 286 2 12 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 196 286 (accept_3_3 23 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 196 286 2 11 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 196 286 (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 196 286 2 10 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 196 286 2 9 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 196 286 (accept_3_3 17 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 286 2 8 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 196 286 (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 286 2 7 98 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 286 2 6 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 196 286 (accept_3_3 11 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 286 2 5 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 286 (Polychromatic418967fa.accept_16_9_4_14_1_1878 9 196 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 286 2 4 98 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 286 2 3 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 286 (accept_3_3 5 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  286 2 2 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 286 (Polychromatic418967fa.accept_19_3_6_1_1_4064 3 196 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 286 2 1 98 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 286 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 196 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 195 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 195 286 13 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 195 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 90 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 195 286 (accept_3_3 89 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 195 286
  (Polychromatic418967fa.accept_19_12_5_1_1_11093 88 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 195 286 (Polychromatic418967fa.accept_21_3_6_13_1_8756 87 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 195 286 (accept_3_3 86 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 195 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 195 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 84 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 195 286 (accept_3_3 83 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 195 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 195 286 (accept_3_3 80 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 195 286 13 6 15 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 195 286 (accept_3_3 77 195 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 286 (Polychromatic418967fa.accept_9_4_6_7_1_286
  76 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 286
  (Polychromatic418967fa.accept_9_3_6_7_1_562 75 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 195 286 (accept_3_3 74 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 195 286 (Polychromatic418967fa.accept_19_15_5_1_1_5360 72 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 286 (accept_3_3 71 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 286 (Polychromatic418967fa.accept_20_10_15_6_1_2149 70 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 195 286 (accept_3_3 68 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 195 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 195 286 13 5 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 195 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 195 286 (Polychromatic418967fa.accept_14_7_13_6_1_1177 63 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 286 (accept_3_3 62 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 286
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 60 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 195 286 (accept_3_3 59 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 195 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 286 (accept_3_3 56 195 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 54 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 286 (accept_3_3 53 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52
  195 286 13 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 195 286 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 286 (accept_3_3 50 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 286 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 286 (accept_3_3 47
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 286 (accept_3_3 44 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 286 (Polychromatic418967fa.accept_12_6_3_10_1_224
  42 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 286 (accept_3_3 41
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 40 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 195 286 13 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 195 286 (accept_3_3 38 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 286 (Polychromatic418967fa.accept_21_15_6_13_1_8776 36 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 286 (accept_3_3 35 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 286
  (Polychromatic418967fa.accept_10_4_5_6_1_651 34 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 286 (accept_3_3 32 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 286 (Polychromatic418967fa.accept_9_3_6_7_1_562
  30 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 286 (accept_3_3 29
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 195 286 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 195 286 13 2 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 195 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 195 286 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 286 (accept_3_3 23 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 195 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 286 (accept_3_3 20
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 286
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 195 286 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 286 (accept_3_3 17 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 195 286 (Polychromatic418967fa.accept_17_16_8_14_1_6757 16 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 286
  (Polychromatic418967fa.accept_19_15_5_1_1_5360 15 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 286 (accept_3_3 14 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13
  195 286 13 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 195 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 286 (accept_3_3 11 195 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 195 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 286 (accept_3_3 8 195
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 286 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 6 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 286 (accept_3_3 5 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 286 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 195 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 286 (accept_3_3 2 195 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 194 286
  (Eq.refl Bool.true) (allA_of_3_1 93 194 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 193 286 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 193 286 (accept_3_3 92 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 193 286
  (Polychromatic418967fa.accept_21_6_4_13_1_8740 90 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 193 286 (accept_3_3 89 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 193 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 193 286 (accept_3_3 86 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 193 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 85 193 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 193 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 193 286 (accept_3_3 83 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 193 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 193 286 (accept_3_3 80 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 193 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 193 286 (accept_3_3 77 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 193 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 286 (accept_3_3 74 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 193 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 193 286 (accept_3_3 71 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 193 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 70 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 286 (accept_3_3 68 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 193 286 (accept_3_3 65 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 193 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 286 (accept_3_3 62 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 286 (accept_3_3 59 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 286 (accept_3_3 56 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 286 (accept_3_3 53 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 286 (accept_3_3 50 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 49 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 286
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 286 (accept_3_3 47 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 286 (accept_3_3 44 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 286 (accept_3_3 41 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 286 (accept_3_3 38 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 286
  (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 286 (accept_3_3 35 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 286 (Polychromatic418967fa.accept_33_1_28_22_1_17598 34 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 286 (accept_3_3 32 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 193 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 286 (accept_3_3 29 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 286 (accept_3_3 26 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 286 (Polychromatic418967fa.accept_15_10_13_1_1_3698 25 193 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 286 (accept_3_3 23 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 286 (Polychromatic418967fa.accept_21_1_4_13_1_7128 22 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 286 (accept_3_3 20 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 286 (accept_3_3 17 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 286 (accept_3_3 14 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 286 (Polychromatic418967fa.accept_16_13_1_14_1_2855 13 193 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 286 (accept_3_3 11 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 286 (accept_3_3 8 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 286
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 286 (accept_3_3 5 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 286 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 193 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 286 (accept_3_3 2 193 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 286 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 192
  286 (Eq.refl Bool.true) (allA_succ_of_gcd 94 192 286 2 47 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 192 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 192 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 192 286 2 46 96 143 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 192 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 91 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 192 286 2 45 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 192 286 (accept_3_3 89 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 192 286 2 44 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 192 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 192 286 2 43 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 192 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 85 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 192 286 2 42 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 192 286 (accept_3_3 83 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 192 286 2 41 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 192 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 192 286 2 40 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 192 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 79 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 286 2 39 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 286 (accept_3_3 77 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 192 286 2 38 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 192 286 (Polychromatic418967fa.accept_19_18_2_1_1_5375 75 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 192 286 2 37 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 192 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 286 2 36 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 192 286 (accept_3_3 71 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 192 286 2 35 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 192 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 69 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 192 286 2 34 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 192 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 286 2 33 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 286 (accept_3_3 65 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 192 286 2 32 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 192 286 (Polychromatic418967fa.accept_18_9_12_16_1_7323 63 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 192 286 2 31 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 192 286
  (Polychromatic418967fa.accept_10_1_2_6_1_638 61 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 286 2 30 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 286 (accept_3_3 59 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 192 286 2 29 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 192 286 (Polychromatic418967fa.accept_20_17_12_6_1_6171 57 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 192 286 2 28 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 286 2 27 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 286 (accept_3_3 53 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 192 286 2 26 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 192 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 192 286 2 25 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 286 2 24 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 286 (accept_3_3 47 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 192 286 2 23 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 192 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 192 286 2 22 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 286
  (Polychromatic418967fa.accept_15_13_12_1_1_1841 43 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 192 286 2 21 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 192 286 (accept_3_3 41 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 192 286 2 20 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 192 286 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 192 286 2 19 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 192 286
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 286 2 18 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 286 (accept_3_3 35 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 192 286 2 17 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 192 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 286 2 16 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 286 2 15 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 286 (accept_3_3 29 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 286 2 14 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 192 286 (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 286 2 13 96 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 286
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 286 2 12 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 286 (accept_3_3 23 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 286 2 11 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 192 286 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 286 2 10 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 286
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 286 2 9 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 286 (accept_3_3 17 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 286 2 8 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 192 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 286 2 7 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 286
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 286 2 6 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 286 (accept_3_3 11 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 286 2 5 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 192 286 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 286 2 4 96 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 286
  (Polychromatic418967fa.accept_19_7_2_1_1_4076 7 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 286 2 3 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 286 (accept_3_3 5 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192
  286 2 2 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  192 286 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 192 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 192 286 2 1 96 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 192 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 192 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 191
  286 (Eq.refl Bool.true) (allA_of_3_1 96 191 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 190 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 96 190 286 2 48 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 190 286 (accept_3_3 95 190 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 94 190 286 2 47 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 93 190 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 190 286 2 46 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 190 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 91 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 190 286 2 45 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 190 286 (accept_3_3 89 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 190 286 2 44 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 190 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 87 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 190 286 2 43 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 190 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 85 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 190 286 2 42 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 190 286 (accept_3_3 83 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 190 286 2 41 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 190 286 (Polychromatic418967fa.accept_15_6_10_1_1_3675 81 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 190 286 2 40 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 190 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 79 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 190 286 2 39 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 190 286 (accept_3_3 77 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 190 286 2 38 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 190 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 190 286 2 37 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 190 286
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 73 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 190 286 2 36 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 190 286 (accept_3_3 71 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 190 286 2 35 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 190 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 69 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 190 286 2 34 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 190 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 190 286 2 33 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 190 286 (accept_3_3 65 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 190 286 2 32 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 190 286 (Polychromatic418967fa.accept_14_7_8_6_1_1164 63 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 190 286 2 31 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 190 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 190 286 2 30 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 190 286 (accept_3_3 59 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 190 286 2 29 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 190 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 190 286 2 28 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 190 286
  (Polychromatic418967fa.accept_18_1_10_16_1_566 55 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 190 286 2 27 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 190 286 (accept_3_3 53 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 190 286 2 26 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 190 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 190 286 2 25 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 190 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 190 286 2 24 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 190 286 (accept_3_3 47 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 190 286 2 23 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 190 286 (Polychromatic418967fa.accept_17_11_3_14_1_6736 45 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 190 286 2 22 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 286
  (Polychromatic418967fa.accept_15_13_10_1_1_1862 43 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 190 286 2 21 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 190 286 (accept_3_3 41 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 286 2 20 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 286 2 19 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 190 286 2 18 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 190 286 (accept_3_3 35 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 190 286 2 17 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 190 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 286 2 16 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 286 2 15 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 286 (accept_3_3 29 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 286 2 14 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 286 (Polychromatic418967fa.accept_23_4_6_10_1_7908 27 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 286 2 13 95 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 190 286
  (Polychromatic418967fa.accept_20_5_10_6_1_6166 25 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 190 286 2 12 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 190 286 (accept_3_3 23 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 286 2 11 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 286 2 10 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 286 2 9 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 286 (accept_3_3 17 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 286 2 8 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 286 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 286 2 7 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 286
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 286 2 6 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 286 (accept_3_3 11 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 286 2 5 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 190 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 286 2 4 95 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 286
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 286 2 3 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 286 (accept_3_3 5 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  286 2 2 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 286 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 190 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 286 2 1 95 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 286 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 190 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  189 286 (Eq.refl Bool.true) (allA_succ_of_accept 97 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 97 189 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 189 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 96 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 189 286 (accept_3_3 95 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 189 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 94 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 189 286 (Polychromatic418967fa.accept_10_3_9_6_1_94 93 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 189 286 (accept_3_3 92 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 91 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 189 286
  (Polychromatic418967fa.accept_12_6_9_10_1_565 90 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 189 286 (accept_3_3 89 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 189 286 (Polychromatic418967fa.accept_17_3_2_14_1_6714 88 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 189 286 (accept_3_3 86 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 189 286
  (Polychromatic418967fa.accept_17_16_2_14_1_6715 84 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 189 286 (accept_3_3 83 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 189 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 82 189 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 286 (Polychromatic418967fa.accept_15_6_9_1_1_1823 81 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 286 (accept_3_3 80 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 78 189 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 286 (accept_3_3 77 189 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 189 286 (Polychromatic418967fa.accept_23_7_5_10_1_9675 76 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 189 286 (accept_3_3 74 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 189 286 (Polychromatic418967fa.accept_23_3_5_10_1_14329 72 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 286 (accept_3_3 71 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 70 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 286
  (Polychromatic418967fa.accept_14_13_7_6_1_3525 69 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 189 286 (accept_3_3 68 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 66 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 286 (accept_3_3 65 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 64 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 189 286 (accept_3_3 62 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 189 286 (Polychromatic418967fa.accept_33_27_24_22_1_17597 60 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 286 (accept_3_3 59 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 286 (Polychromatic418967fa.accept_16_10_13_14_1_5042 58
  189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 286
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 57 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 189 286 (accept_3_3 56 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 54 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 286 (accept_3_3 53 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 286 (Polychromatic418967fa.accept_15_7_9_1_1_473 52 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 189 286 (accept_3_3 50 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 189 286 (Polychromatic418967fa.accept_18_12_9_16_1_4732 48 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 286 (accept_3_3 47 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 286 (Polychromatic418967fa.accept_19_8_18_1_1_17596 46 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 286
  (Polychromatic418967fa.accept_10_5_9_6_1_697 45 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 189 286 (accept_3_3 44 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 42 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 286 (accept_3_3 41 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 40 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 189 286 (accept_3_3 38 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 189 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 286 (accept_3_3 35 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 286 (Polychromatic418967fa.accept_20_14_9_6_1_3346 34 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 286
  (Polychromatic418967fa.accept_10_3_9_6_1_94 33 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 189 286 (accept_3_3 32 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 286 (accept_3_3 29 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 286 (Polychromatic418967fa.accept_25_3_14_11_1_17595 28
  189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 189 286 (accept_3_3 26 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 286 (Polychromatic418967fa.accept_19_5_18_1_1_11052 24 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 286 (accept_3_3 23 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 286 (Polychromatic418967fa.accept_14_8_7_6_1_1159 22 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 286
  (Polychromatic418967fa.accept_15_6_9_1_1_1823 21 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 286 (accept_3_3 20 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 286 (accept_3_3 17 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 286 (Polychromatic418967fa.accept_17_16_2_14_1_6715 16 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 286
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 286 (accept_3_3 14 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 189 286 (Polychromatic418967fa.accept_18_12_9_16_1_4732 12 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 286 (accept_3_3 11 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 286 (Polychromatic418967fa.accept_15_10_9_1_1_3688 10 189
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 286
  (Polychromatic418967fa.accept_24_9_21_22_1_17594 9 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 286 (accept_3_3 8 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 286 (Polychromatic418967fa.accept_12_6_9_10_1_565 6 189 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 286 (accept_3_3 5 189 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 286
  (Polychromatic418967fa.accept_25_4_14_11_1_14134 4 189 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 286 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 286 (accept_3_3 2 189 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  188 286 (Eq.refl Bool.true) (allA_of_3_1 99 188 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 187 286
  (Eq.refl Bool.true) (allA_succ_of_gcd 99 187 286 11 9 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 98 187 286 (accept_3_3 98 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 97 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 187 286 (Polychromatic418967fa.accept_15_6_7_1_1_93
  96 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 187 286 (accept_3_3 95
  187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 187 286
  (Polychromatic418967fa.accept_18_4_7_16_1_2307 94 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 187 286 (accept_3_3 92 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 187 286 (Polychromatic418967fa.accept_10_1_7_6_1_91 91 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 187 286
  (Polychromatic418967fa.accept_21_6_19_13_1_7196 90 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 187 286 (accept_3_3 89 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 187 286 11 8 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 187 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 187 286 (accept_3_3 86 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 187 286
  (Polychromatic418967fa.accept_15_9_7_1_1_1075 84 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 187 286 (accept_3_3 83 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 187 286 (Polychromatic418967fa.accept_23_13_3_10_1_14350 82 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 187 286 (accept_3_3 80 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 187 286 (Polychromatic418967fa.accept_19_3_16_1_1_8246 79 187
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 187 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 187 286 11 7 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 187 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 76 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 187 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 187 286 (accept_3_3 74 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 187 286 (Polychromatic418967fa.accept_19_15_16_1_1_11087 72 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 187 286 (accept_3_3 71 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 187 286 (Polychromatic418967fa.accept_15_10_7_1_1_3686 70 187
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 187 286
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 187 286 (accept_3_3 68 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 187 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 187 286 11 6 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 187 286 (accept_3_3 65 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 187 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 187 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 187 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 286 (accept_3_3 62 187 286
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 286
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 286 (accept_3_3 59 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 286 (Polychromatic418967fa.accept_18_4_7_16_1_2307 58 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 286 (accept_3_3 56 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 55 187 286 11 5 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 187 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 54 187
  286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 187 286 (accept_3_3 53 187
  286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 187 286
  (Polychromatic418967fa.accept_12_4_7_10_1_563 52 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 187 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 286 (accept_3_3 50 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 286
  (Polychromatic418967fa.accept_19_10_16_1_1_8271 48 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 187 286 (accept_3_3 47 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 187 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 187 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 187 286 11 4 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 187 286
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 187 286 (Polychromatic418967fa.accept_19_4_16_1_1_8332 42 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 187 286 (accept_3_3 41 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 187 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 187 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 187 286 (accept_3_3 38 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 187 286 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 286 (accept_3_3 35 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 187 286 (Polychromatic418967fa.accept_19_15_16_1_1_11087 34 187 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 187 286 11 3 17 26 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 187 286 (accept_3_3 32
  187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 286
  (Polychromatic418967fa.accept_10_1_7_6_1_91 31 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 187 286 (Polychromatic418967fa.accept_23_7_3_10_1_2935 30 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 286 (accept_3_3 29 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 187 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 187 286 (accept_3_3 26 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 286 (Polychromatic418967fa.accept_15_9_7_1_1_1075 24 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 286 (accept_3_3 23 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 187 286 11 2 17 26 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 286 (accept_3_3 20
  187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 286
  (Polychromatic418967fa.accept_16_3_11_14_1_446 19 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 187 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 286 (accept_3_3 17 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 187 286 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 286
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 286 (accept_3_3 14 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 286 (Polychromatic418967fa.accept_20_12_7_6_1_6154 12 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 187 286 11 1 17 26 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 187 286
  (Polychromatic418967fa.accept_15_10_7_1_1_3686 10 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 286 (accept_3_3 8 187 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 187 286 (Polychromatic418967fa.accept_21_7_19_13_1_7164 7 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 286
  (Polychromatic418967fa.accept_15_6_7_1_1_93 6 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 286 (accept_3_3 5 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 286 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 187 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 286 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 286 (accept_3_3 2 187 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  286)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 186 286 (Eq.refl Bool.true) (allA_succ_of_gcd 100 186 286 2 50 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 186 286 (Polychromatic418967fa.accept_12_3_6_10_1_576
  99 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 186 286 2 49 93 143
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 186 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 97 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 186 286 2 48 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 186 286 (accept_3_3 95 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 186 286 2 47 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 186 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 186 286 2 46 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 186 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 91 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 186 286 2 45 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 286 (accept_3_3 89 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 186 286 2 44 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 186 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 186 286 2 43 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 186 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 186 286 2 42 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 186 286 (accept_3_3 83 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 186 286 2 41 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 186 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 81 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 186 286 2 40 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 186 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 79 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 186 286 2 39 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 186 286 (accept_3_3 77 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 186 286 2 38 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 186 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 186 286 2 37 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 186 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 73 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 186 286 2 36 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 186 286 (accept_3_3 71 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 186 286 2 35 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 186 286 (Polychromatic418967fa.accept_12_9_6_10_1_1085 69 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 186 286 2 34 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 186 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 286 2 33 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 286 (accept_3_3 65 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 186 286 2 32 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 186 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 186 286 2 31 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 186 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 286 2 30 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 286 (accept_3_3 59 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 186 286 2 29 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 186 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 186 286 2 28 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 286
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 286 2 27 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 286 (accept_3_3 53 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 186 286 2 26 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 186 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 186 286 2 25 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 286 2 24 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 286 (accept_3_3 47 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 186 286 2 23 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 286 2 22 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 286
  (Polychromatic418967fa.accept_19_5_15_1_1_4041 43 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 286 2 21 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 286 (accept_3_3 41 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 286 2 20 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 286 2 19 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 286
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 286 2 18 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 286 (accept_3_3 35 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 286 2 17 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 286 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 286 2 16 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 286
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 286 2 15 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 286 (accept_3_3 29 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 286 2 14 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 286 2 13 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 286
  (Polychromatic418967fa.accept_15_10_6_1_1_3707 25 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 286 2 12 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 286 (accept_3_3 23 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 286 2 11 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 286 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 286 2 10 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 286
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 286 2 9 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 286 (accept_3_3 17 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 286 2 8 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 286 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 286 2 7 93 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 286
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 286 2 6 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 286 (accept_3_3 11 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 286 2 5 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 286 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 186 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 286 2 4 93 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 286
  (Polychromatic418967fa.accept_15_7_6_1_1_1091 7 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 286 2 3 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 286 (accept_3_3 5 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  286 2 2 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 286 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 186 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 286 2 1 93 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 286 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  102 185 286 (Eq.refl Bool.true) (allA_of_3_1 102 185 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 103 184
  286 (Eq.refl Bool.true) (allA_succ_of_gcd 102 184 286 2 51 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 184 286 (accept_3_3 101 184 286 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 184 286 2 50 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 184 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 184 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 184 286 2 49 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 184 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 97 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 184 286 2 48 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 184 286 (accept_3_3 95 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 184 286 2 47 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 184 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 93 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 184 286 2 46 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 184 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 91 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 184 286 2 45 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 184 286 (accept_3_3 89 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 184 286 2 44 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 184 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 184 286 2 43 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 184 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 85 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 184 286 2 42 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 184 286 (accept_3_3 83 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 184 286 2 41 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 184 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 184 286 2 40 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 184 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 79 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 184 286 2 39 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 184 286 (accept_3_3 77 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 184 286 2 38 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 184 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 184 286 2 37 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 184 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 73 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 184 286 2 36 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 184 286 (accept_3_3 71 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 184 286 2 35 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 184 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 184 286 2 34 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 184 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 67 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 184 286 2 33 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 184 286 (accept_3_3 65 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 184 286 2 32 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 184 286 (Polychromatic418967fa.accept_15_3_4_1_1_1072 63 184 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 184 286 2 31 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 184 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 184 286 2 30 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 184 286 (accept_3_3 59 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 184 286 2 29 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 184 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 184 286 2 28 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 184 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 184 286 2 27 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 184 286 (accept_3_3 53 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 184 286 2 26 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 184 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 184 286 2 25 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 184 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 49 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 184 286 2 24 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 184 286 (accept_3_3 47 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 184 286 2 23 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 184 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 184 286 2 22 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 184 286
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 184 286 2 21 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 184 286 (accept_3_3 41 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 184 286 2 20 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 184 286 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 184 286 2 19 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 184 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 184 286 2 18 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 184 286 (accept_3_3 35 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 184 286 2 17 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 184 286 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 286 2 16 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 286
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 286 2 15 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 286 (accept_3_3 29 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 286 2 14 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 184 286 (Polychromatic418967fa.accept_15_12_4_1_1_3746 27 184 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 286 2 13 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 286
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 286 2 12 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 184 286 (accept_3_3 23 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 184 286 2 11 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 286 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 286 2 10 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 286
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 286 2 9 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 286 (accept_3_3 17 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 286 2 8 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 184 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 184 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 286 2 7 92 143 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 286
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 286 2 6 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 184 286 (accept_3_3 11 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 286 2 5 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 286 (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 184 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 286 2 4 92 143 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 286
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 286 2 3 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 286 (accept_3_3 5 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  286 2 2 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 286 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 184 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 286 2 1 92 143 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 286 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 184 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 183 286 (Eq.refl Bool.true) (allA_succ_of_accept 103 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 103 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 183 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 102 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 183 286 (accept_3_3 101 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  100 183 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 100 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 99 183 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 99 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 183 286 (accept_3_3 98 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 97 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 183 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 96 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 183 286 (accept_3_3 95 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 183 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 94 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 93 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 183 286 (accept_3_3 92 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 183 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 90 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 183 286 (accept_3_3 89 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 183 286 (Polychromatic418967fa.accept_10_8_3_6_1_685 88 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 183 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 87 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 183 286 (accept_3_3 86 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 183 286
  (Polychromatic418967fa.accept_16_4_7_14_1_3897 84 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 183 286 (accept_3_3 83 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 183 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 183 286 (accept_3_3 80 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 183 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 78 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 183 286 (accept_3_3 77 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 183 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 183 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 286 (accept_3_3 74 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 183 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 183 286 (accept_3_3 71 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 183 286 (Polychromatic418967fa.accept_19_13_12_1_1_3993 70 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 286 (accept_3_3 68 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 183 286
  (Polychromatic418967fa.accept_12_6_3_10_1_224 66 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 183 286 (accept_3_3 65 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 183 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 183 286 (Polychromatic418967fa.accept_14_7_1_6_1_3514 63 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 286 (accept_3_3 62 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 183 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 183 286 (accept_3_3 59 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 183 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 286 (accept_3_3 56 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 183 286 (accept_3_3 53 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 183 286 (Polychromatic418967fa.accept_16_4_7_14_1_3897 52 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 183 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 286 (accept_3_3 50 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 48 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 183 286 (accept_3_3 47 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 183 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 286 (accept_3_3 44 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 183 286 (accept_3_3 41 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 183 286 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 183 286 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 286 (accept_3_3 38 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 286
  (Polychromatic418967fa.accept_15_6_3_1_1_3678 36 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 286 (accept_3_3 35 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 286 (Polychromatic418967fa.accept_15_4_3_1_1_487 34 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 286 (accept_3_3 32 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 286
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 286 (accept_3_3 29 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 286 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 286 (accept_3_3 26 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 286 (accept_3_3 23 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 286 (accept_3_3 20 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 286
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 286 (accept_3_3 17 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 286 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 286 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 286 (accept_3_3 14 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 286
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 286 (accept_3_3 11 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 286 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 286 (accept_3_3 8 183 286 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 286 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 286
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 286 (accept_3_3 5 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 286 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 183 286 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 286 (Polychromatic418967fa.accept_24_3_15_22_1_17593 3 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 286 (accept_3_3 2 183 286 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 286 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 286
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  286))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_286_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


