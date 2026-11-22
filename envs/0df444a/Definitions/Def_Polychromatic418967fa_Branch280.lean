-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch280
-- name    : Polychromatic418967fa_Branch280
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:34:04.627085+00:00
-- url     : https://prove2.me/theorems/a64df7bf-3fe2-43ac-9e63-2b51eaabf4db
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch280_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_280 : allB 280 280 :=
  allB_succ' 2 279 280 (Eq.refl Bool.true) (allA_succ_of_accept 1 279 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  279 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 279 280)) (allB_succ' 3 278 280
  (Eq.refl Bool.true) (allA_of_3_1 3 278 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 277 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 277 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 277 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 277 280 (accept_3_3 2 277 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 277 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 277 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 277 280)))) (allB_succ' 5 276 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 276 280 4 1 69 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 276 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 276 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 276 280 2 1 138 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1
  276 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 276 280))))) (allB_succ' 6 275 280
  (Eq.refl Bool.true) (allA_of_3_1 6 275 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 274 280 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 274 280 2 3 137 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 274 280 (accept_3_3 5 274 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 274 280 2 2 137 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 274 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 274 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 274 280 2 1 137 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 274 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 274 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 274 280))))))) (allB_succ' 8 273 280 (Eq.refl Bool.true) (allA_succ_of_gcd 7 273 280 7 1 39 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 273 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 273 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 273 280 (accept_3_3 5 273 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  273 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 273 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 273 280 (Polychromatic418967fa.accept_19_3_7_14_1_3669 3 273 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 273 280 (accept_3_3 2 273 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 273 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 273 280)))))))) (allB_succ' 9 272 280 (Eq.refl
  Bool.true) (allA_of_3_1 9 272 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 271 280 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 271 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 271 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 271 280 (accept_3_3 8 271 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 271 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 271 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 271 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549
  6 271 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 271 280 (accept_3_3 5
  271 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 271 280
  (Polychromatic418967fa.accept_13_4_11_7_1_558 4 271 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 271 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 271 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 271 280 (accept_3_3 2 271 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 271 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 271 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 271 280)))))))))) (allB_succ' 11 270 280 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 270 280 10 1 27 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 270 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 270 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 270 280 2 4 135 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 270 280
  (Polychromatic418967fa.accept_19_7_4_14_1_5003 7 270 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 270 280 2 3 135 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 270 280 5 1 54 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 270 280 2 2 135 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 270 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 270 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 270 280 2 1 135 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 280
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 270 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 280))))))))))) (allB_succ' 12 269 280 (Eq.refl Bool.true) (allA_of_3_1 12 269 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 268 280 (Eq.refl Bool.true) (allA_succ_of_gcd 12 268 280 4 3 67 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 268 280 (accept_3_3 11
  268 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 268 280 2 5 134 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 268 280
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 268 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 268 280 4 2 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 268 280 (Polychromatic418967fa.accept_16_7_12_8_1_2450 7 268 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 268 280 2 3 134 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 268 280 (accept_3_3 5 268 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 268 280 4 1 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 268 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 268 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 268 280 2 1 134 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 268 280
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 268 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 268 280))))))))))))) (allB_succ' 14 267 280 (Eq.refl Bool.true) (allA_succ_of_accept 13 267 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 267 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 267 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 267 280 (accept_3_3 11 267 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 267 280 (Polychromatic418967fa.accept_17_10_12_8_1_2748 10 267 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 267 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 267 280 (accept_3_3 8 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  267 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 267 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 267 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 267 280 (accept_3_3 5 267 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 267 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 267 280 (accept_3_3 2 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  267 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 267 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 267 280)))))))))))))) (allB_succ' 15 266 280 (Eq.refl Bool.true) (allA_of_3_1 15 266 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 265 280 (Eq.refl Bool.true) (allA_succ_of_gcd 15 265 280 5 3
  53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 265 280
  (accept_3_3 14 265 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 265 280
  (Polychromatic418967fa.accept_19_13_18_14_1_3522 13 265 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 265 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 265 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 280 (accept_3_3 11 265 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 265 280 5 2 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 265 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 265 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 265 280 (accept_3_3 8 265 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 265 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7
  265 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 265 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 265 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 265 280 5 1 53 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 265 280 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 265 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 265 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 280 (accept_3_3 2 265 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 265 280 (Polychromatic418967fa.accept_16_1_9_8_1_2438
  1 265 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 265 280)))))))))))))))) (allB_succ'
  17 264 280 (Eq.refl Bool.true) (allA_succ_of_gcd 16 264 280 8 2 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 264 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 264 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 264 280 2 7 132 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 264 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 264 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 264 280 4 3 66 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 264 280 (accept_3_3 11 264 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  264 280 2 5 132 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 264 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 264 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 264 280 8 1 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 264 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 264 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264 280 2 3 132 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 264 280 (accept_3_3 5
  264 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 264 280 4 1 66 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 264 280
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 264 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 264 280 2 1 132 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 264 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 1 264 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264 280))))))))))))))))) (allB_succ' 18 263 280 (Eq.refl Bool.true)
  (allA_of_3_1 18 263 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 262 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 262 280 2 9 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 262 280 (accept_3_3 17 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 262 280 2 8 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 262 280 (Polychromatic418967fa.accept_21_15_10_7_1_9837 15 262 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 262 280 2 7 131 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 262 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 262 280 2 6 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 262 280 (accept_3_3 11 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 262 280 2 5 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 262 280 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 262 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 262 280 2 4 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 262 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 262 280 2 3 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 262 280 (accept_3_3 5 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 262 280 2 2 131 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 262 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 3 262 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 262 280 2 1 131 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 262 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 262 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 262 280))))))))))))))))))) (allB_succ' 20 261 280 (Eq.refl Bool.true) (allA_succ_of_accept 19 261 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 261 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 261 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 261 280 (accept_3_3 17 261 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 261 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 261 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 261 280
  (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 261 280 (accept_3_3 14 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 261 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 261 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 261 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 280 (accept_3_3 11 261 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 261 280 (Polychromatic418967fa.accept_21_10_9_7_1_9857 10 261
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 261 280
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 261 280 (accept_3_3 8 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  261 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 261 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 261 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 280 (accept_3_3 5 261 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 280 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 261 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 3 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 261 280 (accept_3_3 2 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  261 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 261 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 261 280)))))))))))))))))))) (allB_succ' 21 260 280 (Eq.refl Bool.true) (allA_of_3_1 21 260 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 259 280 (Eq.refl Bool.true) (allA_succ_of_gcd 21 259 280 7 3
  37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 259 280
  (accept_3_3 20 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 259 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 259 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 259 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 259 280 (accept_3_3 17 259 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 259 280 (Polychromatic418967fa.accept_19_16_12_14_1_10640 16 259 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 259 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 259 280 7 2 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 259 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 259 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 259 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 259 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 259 280 (accept_3_3 11 259 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 259 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 259 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 259 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 280 (accept_3_3 8 259 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 259 280 7 1 37 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 259 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 259 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 259 280 (accept_3_3 5 259 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 259 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 259 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 259 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 259 280 (accept_3_3 2 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  259 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 259 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 259 280)))))))))))))))))))))) (allB_succ' 23 258 280 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  258 280 2 11 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 258 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 258 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 258 280 2 10 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 258 280
  (Polychromatic418967fa.accept_23_19_5_4_1_12535 19 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 258 280 2 9 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 258 280 (accept_3_3 17 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 258 280 2 8 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 258 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 258 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 258 280 2 7 129 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 258 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 258 280 2 6 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 258 280 (accept_3_3 11 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 258 280 2 5 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 258 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 258 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 258 280 2 4 129 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 280 2 3 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 258 280 (accept_3_3 5 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 258 280 2 2 129 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 258 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 258 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 258 280 2 1 129 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 258 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 258 280))))))))))))))))))))))) (allB_succ' 24 257 280 (Eq.refl Bool.true) (allA_of_3_1 24 257 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 256 280 (Eq.refl Bool.true) (allA_succ_of_gcd 24 256 280 8 3 32 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 256 280
  (accept_3_3 23 256 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 256 280 2 11 128 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 256 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 256 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 256 280 4 5 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 256 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 256 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 256 280 2 9 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 256 280 (accept_3_3 17 256 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 256 280 8 2 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 256 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 256 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 256 280 2 7 128 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 256 280
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 256 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 256 280 4 3 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 256 280 (accept_3_3 11 256 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  256 280 2 5 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 256 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 256 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 256 280 8 1 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 256 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 256 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 256 280 2 3 128 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 256 280 (accept_3_3 5
  256 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 256 280 4 1 64 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 256 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 256 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 256 280 2 1 128 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 256 280 (Polychromatic418967fa.accept_19_1_9_14_1_526 1 256 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 280))))))))))))))))))))))))) (allB_succ' 26 255 280 (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 255 280 5 5 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 24 255 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 255 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 255 280 (accept_3_3 23 255 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 255 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 280
  (Polychromatic418967fa.accept_19_2_8_14_1_3648 21 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 255 280 5 4 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 255 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 255 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 255 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 255
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 280 (accept_3_3 17 255
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 16 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 255 280 5 3 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 255 280 (accept_3_3 14 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 255 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 255 280 (Polychromatic418967fa.accept_13_12_8_7_1_2526 12 255 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 280 (accept_3_3 11 255 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 255 280 5 2 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 255 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9
  255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 280 (accept_3_3 8 255
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 255 280 5 1 51 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 255 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 255 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 255 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 280 (accept_3_3 2 255 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  255 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 280))))))))))))))))))))))))))
  (allB_succ' 27 254 280 (Eq.refl Bool.true) (allA_of_3_1 27 254 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 28 253 280 (Eq.refl Bool.true) (allA_succ_of_accept 27 253 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  27 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 253 280 (accept_3_3 26
  253 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 253 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 25 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 253 280 (Polychromatic418967fa.accept_19_5_6_14_1_5010 24 253 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 253 280 (accept_3_3 23 253 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 253 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 253 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 253 280 (accept_3_3 20 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 253 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 253 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 253 280 (accept_3_3 17 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 253 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 253
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 253 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 253 280 (accept_3_3 14 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 253 280 (Polychromatic418967fa.accept_17_13_15_8_1_3860 13 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 253 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 280 (accept_3_3 11 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 253
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 280 (accept_3_3 8 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 280 (Polychromatic418967fa.accept_19_7_6_14_1_11872 7 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 280 (Polychromatic418967fa.accept_17_6_15_8_1_1714 6 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 280 (accept_3_3 5 253 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 280 (Polychromatic418967fa.accept_13_4_6_7_1_2471 4 253 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 280 (accept_3_3 2 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 253 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 280)))))))))))))))))))))))))))) (allB_succ' 29 252 280 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 252 280 28 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 252 280 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 252 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 252 280 2 13 126 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 252 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 252 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 252 280 4 6 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 252 280 (accept_3_3 23 252 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  252 280 2 11 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 252 280 7 3 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 252 280 4 5 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 252 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 19 252 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 252 280 2 9 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 252 280 (accept_3_3 17 252 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 252 280 4 4 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 252 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 252
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 280 14 1 18 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 280
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 252 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 252 280 4 3 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 252 280 (accept_3_3 11 252 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 252 280 2 5 126 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 252 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 252 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 252 280 4 2 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 252 280 7 1 36 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 252 280 2 3 126 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 252 280 (accept_3_3 5 252 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 252 280 4 1 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 252 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 3 252 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 280 2 1 126 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 252 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 280))))))))))))))))))))))))))))) (allB_succ' 30 251 280 (Eq.refl Bool.true) (allA_of_3_1 30 251 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 250 280 (Eq.refl Bool.true) (allA_succ_of_gcd 30 250 280 10 3
  25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 250 280
  (accept_3_3 29 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 250 280 2 14 125 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 250 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 250 280 2 13 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 250 280 5 5 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 250 280 2 12 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 250 280 (accept_3_3 23 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 250 280 2 11 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 250 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 250 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 250 280 10 2 25 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 250 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 250 280 2 9 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 250 280 (accept_3_3 17 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 250 280 2 8 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 250 280 5 3 50 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 250 280 2 7 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 250 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 250 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 250 280 2 6 125 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 250 280 (accept_3_3 11 250 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 250 280 10 1 25 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 250 280
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 250 280 2 4 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 250 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 250 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 250 280 2 3 125 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 250 280 5 1 50 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 250 280 2 2 125 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 250 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 250 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 250 280 2 1 125 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 250 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1 250 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 250 280))))))))))))))))))))))))))))))) (allB_succ' 32 249 280
  (Eq.refl Bool.true) (allA_succ_of_accept 31 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 249 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 249 280 (accept_3_3 29 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 249 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 249 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 249 280 (accept_3_3 26 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 249 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 249 280
  (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 249 280 (accept_3_3 23 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 249 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 249 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 249 280 (accept_3_3 20 249 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 249 280 (accept_3_3 17 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 249 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 249 280 (Polychromatic418967fa.accept_16_15_9_8_1_2440 15 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 249 280 (accept_3_3 14 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 249 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 249 280 (accept_3_3 11 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 249 280 (Polychromatic418967fa.accept_21_10_18_7_1_5212 10 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 249 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 249 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 249 280 (accept_3_3 8 249 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 249 280 (accept_3_3 5 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  249 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 249 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 249 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 249 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 280 (accept_3_3 2 249 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 249 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 280)))))))))))))))))))))))))))))))) (allB_succ' 33
  248 280 (Eq.refl Bool.true) (allA_of_3_1 33 248 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 247 280
  (Eq.refl Bool.true) (allA_succ_of_accept 33 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 247 280 (accept_3_3 32 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 247 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 247
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 247 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 247 280 (accept_3_3 29 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 247 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 28 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 247 280 (accept_3_3 26 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 247 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 247 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 247 280 (accept_3_3 23 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 247 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 247 280 (accept_3_3 20 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 247 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 247 280
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 247 280 (accept_3_3 17 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 247 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 247 280 (accept_3_3 14 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 247 280 (Polychromatic418967fa.accept_21_13_16_7_1_3712 13 247 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 247 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 247 280 (accept_3_3 11 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 247 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 280 (accept_3_3 8 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 280 (accept_3_3 5 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 247 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 280 (accept_3_3 2 247 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 247 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 280)))))))))))))))))))))))))))))))))) (allB_succ' 35
  246 280 (Eq.refl Bool.true) (allA_succ_of_gcd 34 246 280 2 17 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 246 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 246 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 246 280 2 16 123 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 246 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 31 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 246 280 2 15 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 246 280 (accept_3_3 29 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 246 280 2 14 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 246 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 246 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 246 280 2 13 123 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 246 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 246 280 2 12 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 246 280 (accept_3_3 23 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 246 280 2 11 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 246 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 246 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 246 280 2 10 123 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 246 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 280 2 9 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 246 280 (accept_3_3 17 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 246 280 2 8 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 246 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 246 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 246 280 2 7 123 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 246 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 280 2 6 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 280 (accept_3_3 11 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 246 280 2 5 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 246 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 246 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 246 280 2 4 123 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 280 2 3 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 280 (accept_3_3 5 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 246 280 2 2 123 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 246 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 246 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 246 280 2 1 123 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 280
  (Polychromatic418967fa.accept_15_1_6_10_1_23 1 246 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 280))))))))))))))))))))))))))))))))))) (allB_succ' 36 245 280 (Eq.refl Bool.true) (allA_of_3_1 36 245
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 244 280 (Eq.refl Bool.true) (allA_succ_of_gcd 36 244 280 4
  9 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 244
  280 (accept_3_3 35 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 244 280 2 17 122 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 244 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 33 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 244 280 4 8 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 244 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 31 244 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 244 280 2 15 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 244 280 (accept_3_3 29 244 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 244 280 4 7 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 244 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 244
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 244 280 2 13 122 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 244 280
  (Polychromatic418967fa.accept_13_12_10_7_1_2433 25 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 244 280 4 6 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 244 280 (accept_3_3 23 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 244 280 2 11 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 244 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 244 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 244 280 4 5 61 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 244 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 244 280 2 9 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 244 280 (accept_3_3 17 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 244 280 4 4 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 244 280 (Polychromatic418967fa.accept_16_15_4_8_1_1562 15 244 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 244 280 2 7 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 244 280 (Polychromatic418967fa.accept_15_13_4_10_1_821
  13 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 244 280 4 3 61 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 244 280
  (accept_3_3 11 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 244 280 2 5 122 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 244 280
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 244 280 4 2 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 244 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 244 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 244 280 2 3 122 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 280 (accept_3_3 5 244 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 280 4 1 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 244 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 244 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 280 2 1 122 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 244 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 244 280))))))))))))))))))))))))))))))))))))) (allB_succ' 38 243 280 (Eq.refl Bool.true) (allA_succ_of_accept
  37 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 243 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 243 280 (accept_3_3 35 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 34 243
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 243 280 (accept_3_3 32 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 243 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 243 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 30 243
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 243 280 (accept_3_3 29 243
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 243 280 (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 243 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 280 (accept_3_3 26 243 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 243 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 243 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 243 280 (accept_3_3 23 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 243 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 243 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 280 (accept_3_3 20 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 243 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 243 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 243 280 (accept_3_3 17 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 243 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 243 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 15 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 280 (accept_3_3 14 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 243 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 243 280
  (Polychromatic418967fa.accept_16_12_3_8_1_5729 12 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 243 280 (accept_3_3 11 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 243 280 (Polychromatic418967fa.accept_19_10_15_14_1_5016 10 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 280 (accept_3_3 8 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 243 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 243 280 (accept_3_3 5 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  243 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 243 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 243 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 243 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 280 (accept_3_3 2 243 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 243 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 280))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 242 280 (Eq.refl Bool.true) (allA_of_3_1 39 242 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 241 280 (Eq.refl Bool.true) (allA_succ_of_accept 39 241 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 241 280 (accept_3_3 38
  241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 241 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 241 280 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 241 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 241 280 (accept_3_3 35 241 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 241 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 241 280 (accept_3_3 32 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 241 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 241 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 241 280 (accept_3_3 29 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 241 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 241 280 (accept_3_3 26 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 241 280 (Polychromatic418967fa.accept_16_9_1_8_1_5766 25 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 241 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 241 280 (accept_3_3 23 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 241 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 241 280 (accept_3_3 20 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 241 280 (Polychromatic418967fa.accept_21_19_10_7_1_8384 19 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 241 280 (Polychromatic418967fa.accept_19_18_13_14_1_4995 18 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 241 280 (accept_3_3 17 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 241 280 (Polychromatic418967fa.accept_19_16_13_14_1_3616 16
  241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 241 280 (accept_3_3 14 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 241 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 241 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 241 280 (accept_3_3 11 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 241 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 241 280 (accept_3_3 8 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  241 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 241 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 280 (accept_3_3 5 241 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 241 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 280 (accept_3_3 2 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 280 (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 241 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 280)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 240 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 240 280 40 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 240 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 240 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 240 280 2 19 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 240 280 (Polychromatic418967fa.accept_21_16_9_7_1_6709
  37 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 240 280 4 9 60 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 240 280 5 7 48 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 240 280 2 17 120
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 240 280
  (Polychromatic418967fa.accept_17_16_2_8_1_7625 33 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 240 280 8 4 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 240 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 240 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 240 280 10 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 240 280 (accept_3_3 29 240 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 240 280 4 7 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 240 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 240 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 280 2 13 120 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 240 280 5 5 48 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 240 280 8 3 30 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 280 (accept_3_3 23
  240 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 240 280 2 11 120 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 240 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 240 280 20 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 240 280 (Polychromatic418967fa.accept_21_19_9_7_1_8366 19 240 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 280 2 9 120 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 280 (accept_3_3 17 240 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 240 280 8 2 30 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 240 280 5 3 48 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 240 280 2 7 120 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 240 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 280 4 3 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 240 280 (accept_3_3 11 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  240 280 10 1 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 240 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 240 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 280 8 1 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 240 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 280 2 3 120 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 240 280 5 1 48 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 240 280 4 1 60 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 240 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 280 2 1 120 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 1 240 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 280))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 239
  280 (Eq.refl Bool.true) (allA_of_3_1 42 239 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 238 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 238 280 14 3 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 238 280 (accept_3_3 41 238 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 238 280 2 20 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 238 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 238 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 238 280 2 19 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 238 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 238 280 2 18 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 238 280 7 5 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 238 280 2 17 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 238 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 238 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 238 280 2 16 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 238 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 31 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 238 280 2 15 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 238 280 (accept_3_3 29 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 238 280 14 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 238 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 238 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 238 280 2 13 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 238 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 238 280 2 12 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 238 280 (accept_3_3 23 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 238 280 2 11 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 238 280 7 3 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 238 280 2 10 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 238 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 238 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 238 280 2 9 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 238 280 (accept_3_3 17 238 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 238 280 2 8 119 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 238 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 238 280 14 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 238 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 238 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 238 280 2 6 119 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 238 280 (accept_3_3 11 238 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 238 280 2 5 119 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 238 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 238 280 2 4 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 238 280 7 1 34 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 238 280 2 3 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 238 280 (accept_3_3 5 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 280 2 2 119 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 238 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 280 2 1 119 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 238 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 280))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 237 280 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 237 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 237 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 237 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 237 280 (accept_3_3 41 237 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 280 (Polychromatic418967fa.accept_9_4_3_1_1_154
  40 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 237 280 (accept_3_3 38 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 237 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 280 (accept_3_3 35 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 237 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 237 280 (accept_3_3 32 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 237 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 280 (accept_3_3 29 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 280 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 237 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 237 280 (accept_3_3 26 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 237 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 280 (accept_3_3 23 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 237 280 (accept_3_3 20 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 237 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 280 (accept_3_3 17 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 237 280 (accept_3_3 14 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 237 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 280 (accept_3_3 11 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 237
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 280
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 9 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 237 280 (accept_3_3 8 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 237 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 280 (accept_3_3 5 237 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 237 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 280
  (Polychromatic418967fa.accept_16_3_13_8_1_1594 3 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 280 (accept_3_3 2 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 237 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 280)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 236 280 (Eq.refl Bool.true)
  (allA_of_3_1 45 236 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 235 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 235 280 5 9 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 235 280 (accept_3_3 44 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 235 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 43 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 235 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 235 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 235 280 (accept_3_3 41 235 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 235 280 5 8 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 235 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 235 280 (accept_3_3 38
  235 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 235 280
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 235 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 235 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 235 280 5 7 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 235 280 (Polychromatic418967fa.accept_12_10_7_4_1_820
  34 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 235 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 235 280 (accept_3_3 32 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 235 280 (Polychromatic418967fa.accept_18_13_1_10_1_4331 31 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 235 280 5 6 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 235 280 (accept_3_3 29 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 235 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 28 235 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 235 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 235 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 235 280 (accept_3_3 26 235 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 235 280 5 5 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 235 280
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 235 280 (accept_3_3 23 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 235 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 235 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 235 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 235 280 5 4 47 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 235 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 235 280 (Polychromatic418967fa.accept_19_18_7_14_1_5012 18 235 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 280 (accept_3_3 17 235 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 16 235 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 235 280 5 3 47 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 235 280 (accept_3_3 14 235 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 280
  (Polychromatic418967fa.accept_16_13_11_8_1_2449 13 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 280 (Polychromatic418967fa.accept_16_12_11_8_1_832 12 235 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 280 (accept_3_3 11 235 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 235 280 5 2 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 235 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9
  235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 280 (accept_3_3 8 235
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 280
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 235 280 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 235 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 235 280 5 1 47 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 235 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 235 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 280 (accept_3_3 2 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 280 (Polychromatic418967fa.accept_21_1_4_7_1_3689 1 235 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 280)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 234 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 234 280 2 23 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 234 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 234 280 2 22 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 234 280
  (Polychromatic418967fa.accept_19_5_6_14_1_5010 43 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 234 280 2 21 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 234 280 (accept_3_3 41 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 234 280 2 20 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 234 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 234 280 2 19 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 234 280
  (Polychromatic418967fa.accept_17_3_13_8_1_11337 37 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 234 280 2 18 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 234 280 (accept_3_3 35 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 234 280 2 17 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 234 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 234 280 2 16 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 31 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 234 280 2 15 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 234 280 (accept_3_3 29 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 234 280 2 14 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 234 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 234 280 2 13 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 280
  (Polychromatic418967fa.accept_21_4_3_7_1_11420 25 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 234 280 2 12 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 234 280 (accept_3_3 23 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 234 280 2 11 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 234 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 280 2 10 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 280 2 9 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 280 (accept_3_3 17 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 280 2 8 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 234 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 280 2 7 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 280
  (Polychromatic418967fa.accept_22_13_14_16_1_6124 13 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 234 280 2 6 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 234 280 (accept_3_3 11 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 280 2 5 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 280 2 4 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 280
  (Polychromatic418967fa.accept_19_7_6_14_1_11872 7 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 280 2 3 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 280 (accept_3_3 5 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 280 2 2 117 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 234 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 280 2 1 117 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 1 234 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 280))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 233 280 (Eq.refl Bool.true)
  (allA_of_3_1 48 233 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 232 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 232 280 8 6 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 232 280 (accept_3_3 47 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  232 280 2 23 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 232 280 (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 232 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 232 280 4 11 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 232 280 (Polychromatic418967fa.accept_13_4_11_7_1_558
  43 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 232 280 2 21 116 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 232 280
  (accept_3_3 41 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 232 280 8 5 29 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 232 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 232 280 2 19 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 232 280 (Polychromatic418967fa.accept_18_1_16_10_1_2065 37 232 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 232 280 4 9 58 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 232 280 (accept_3_3 35 232 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 232 280 2 17 116 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 232 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 232 280 8 4 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 232 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 232 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 232 280 2 15 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 232 280 (accept_3_3 29 232 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 232 280 4 7 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 232 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 232
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 232 280 2 13 116 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 25 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 232 280 8 3 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 232 280 (accept_3_3 23 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 232 280 2 11 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 232 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 232 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 232 280 4 5 58 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 232 280
  (Polychromatic418967fa.accept_15_4_7_10_1_807 19 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 232 280 2 9 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 232 280 (accept_3_3 17 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 232 280 8 2 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 232 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 232 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 280 2 7 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13
  232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 232 280 4 3 58 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 232 280 (accept_3_3 11
  232 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 232 280 2 5 116 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 232 280
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 232 280 8 1 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 232 280 (Polychromatic418967fa.accept_19_7_4_14_1_5003 7 232 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 280 2 3 116 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 280 (accept_3_3 5 232 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 280 4 1 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 232 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 232 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 280 2 1 116 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 280
  (Polychromatic418967fa.accept_13_1_11_7_1_1704 1 232 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 280))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 231 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 49 231 280 7 7 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 48 231 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 231 280 (accept_3_3 47 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 231 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 231 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 280
  (Polychromatic418967fa.accept_18_9_15_10_1_395 45 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 231 280 (accept_3_3 44 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 231 280 7 6 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 231 280 (accept_3_3 41 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 231 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 280 (accept_3_3 38 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37
  231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 231 280
  (Polychromatic418967fa.accept_16_4_7_8_1_5753 36 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 231 280 7 5 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 231 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 231
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 280 (accept_3_3 32 231
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 231 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 231 280 (accept_3_3 29 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  231 280 7 4 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 231 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 231 280 (accept_3_3 26 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 280 (Polychromatic418967fa.accept_18_6_15_10_1_6975 24 231
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 280 (accept_3_3 23 231
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 22 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 231 280 7 3 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 231 280 (accept_3_3 20 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 231 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 231 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 280 (accept_3_3 17 231 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 280
  (Polychromatic418967fa.accept_16_15_7_8_1_8189 15 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 231 280 7 2 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 231 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 280 (accept_3_3 11 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 280
  (Polychromatic418967fa.accept_24_10_15_16_1_6986 10 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 231 280 (Polychromatic418967fa.accept_16_9_7_8_1_1588 9 231 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 280 (accept_3_3 8 231 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 231 280 7 1 33 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 231 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 231 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 280 (accept_3_3 5 231 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 231 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 280 (accept_3_3 2 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 231 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 280)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 230 280 (Eq.refl
  Bool.true) (allA_of_3_1 51 230 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 229 280 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 229 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 229 280 (accept_3_3 50 229 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 229 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 229 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 229 280 (accept_3_3 47 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 229 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 229 280 (accept_3_3 44 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 229 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 229 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 229 280 (accept_3_3 41 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 229 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 229 280 (accept_3_3 38 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 229 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 229 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 229 280
  (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 229 280 (accept_3_3 35 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 229 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 229 280 (accept_3_3 32 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 229 280 (Polychromatic418967fa.accept_21_10_19_7_1_3719 31 229 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 229 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 229 280 (accept_3_3 29 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 229 280 (Polychromatic418967fa.accept_13_2_8_7_1_2424 28 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 280 (accept_3_3 26 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 229 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 229 280 (accept_3_3 23 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 280 (accept_3_3 20 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 280 (Polychromatic418967fa.accept_16_3_5_8_1_4543 19 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 280 (accept_3_3 17 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 280 (accept_3_3 14 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 229 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 280 (accept_3_3 11 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 280 (accept_3_3 8 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 280 (accept_3_3 5 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 280 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 229 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 280 (accept_3_3 2 229 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 229 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229
  280)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 228 280 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 228 280 4 13 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 228 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 228 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 228 280 2 25 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 228 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 49
  228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 228 280 4 12 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 228 280 (accept_3_3 47
  228 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 228 280 2 23 114 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 228 280
  (Polychromatic418967fa.accept_16_13_4_8_1_4557 45 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 228 280 4 11 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 228 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 228 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 228 280 2 21 114 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 228 280 (accept_3_3 41 228 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 228 280 4 10 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 228 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312
  39 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 228 280 2 19 114 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 280
  (Polychromatic418967fa.accept_15_7_3_10_1_817 37 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 228 280 4 9 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 228 280 (accept_3_3 35 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  228 280 2 17 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 228 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 228 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 280 4 8 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31
  228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 280 2 15 114 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 280
  (accept_3_3 29 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 280 4 7 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 228 280
  (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 228 280 2 13 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 228 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 228 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 280 4 6 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 280 (accept_3_3 23 228 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 280 2 11 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 280 (Polychromatic418967fa.accept_15_6_3_10_1_2341
  21 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 280 4 5 57 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 280
  (Polychromatic418967fa.accept_16_3_4_8_1_3450 19 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 280 2 9 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 228 280 (accept_3_3 17 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 228 280 4 4 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 228 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 228 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 280 2 7 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 280 4 3 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 280 (accept_3_3 11
  228 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 280 2 5 114 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 280
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 280 4 2 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 228 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 228 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 280 2 3 114 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 280 (accept_3_3 5 228 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 280 4 1 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 228 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 228 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 280 2 1 114 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 228 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 280))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 227 280 (Eq.refl Bool.true)
  (allA_of_3_1 54 227 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 226 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 226 280 2 27 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 226 280 (accept_3_3 53 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 226 280 2 26 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 226 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 226 280 2 25 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 226 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 226 280 2 24 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 226 280 (accept_3_3 47 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 226 280 2 23 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 226 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 226 280 2 22 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 226 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 226 280 2 21 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 226 280 (accept_3_3 41 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 226 280 2 20 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 226 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 226 280 2 19 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 226 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 226 280 2 18 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 226 280 (accept_3_3 35 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 226 280 2 17 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 226 280 (Polychromatic418967fa.accept_21_12_16_7_1_14243 33 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 226 280 2 16 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 226 280 2 15 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 226 280 (accept_3_3 29 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 280 2 14 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 280 (Polychromatic418967fa.accept_21_6_16_7_1_3714 27 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 280 2 13 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 280 2 12 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 280 (accept_3_3 23 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 280 2 11 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 280 2 10 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 280 2 9 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 280 (accept_3_3 17 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 280 2 8 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 226 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 280 2 7 113 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 280 2 6 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 280 (accept_3_3 11 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 280 2 5 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 226 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 280 2 4 113 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 280 2 3 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 280 (accept_3_3 5 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 280 2 2 113 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 280 (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 226 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 280 2 1 113 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 280
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 226 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 280))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 225 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 225 280 5 11 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 225 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 225 280 (accept_3_3 53 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 225 280 (Polychromatic418967fa.accept_16_4_1_8_1_835 52 225 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 225 280
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 51 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 225 280 5 10 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 225 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694
  48 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 225 280 (accept_3_3 47
  225 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 280
  (Polychromatic418967fa.accept_17_12_4_8_1_5073 46 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 225 280 5 9 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 225 280 (accept_3_3 44 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 225 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 42 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 280 (accept_3_3 41 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 225 280 5 8 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 225 280 (Polychromatic418967fa.accept_16_7_1_8_1_5796 39 225
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 280 (accept_3_3 38 225
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  37 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 280
  (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 225 280 5 7 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 225 280 (Polychromatic418967fa.accept_21_13_15_7_1_5209 34 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 33 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 225 280 (accept_3_3 32 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 225 280 5 6 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 280 (accept_3_3 29 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 225 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 280
  (Polychromatic418967fa.accept_24_3_9_16_1_8812 27 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 225 280 (accept_3_3 26 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  225 280 5 5 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 225 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 280 (accept_3_3 23 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 22 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 280 (Polychromatic418967fa.accept_19_2_16_14_1_3551 21 225
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 225 280 5 4 45 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 225 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 225 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 280 (accept_3_3 17 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 225 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 225 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 280 5 3 45 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 280 (accept_3_3 14 225 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 280
  (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 280 (accept_3_3 11 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  225 280 5 2 45 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 225 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 280 (accept_3_3 8 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 225 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 225 280 5 1 45 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 225 280
  (Polychromatic418967fa.accept_16_4_1_8_1_835 4 225 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 225 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 3 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 280 (accept_3_3 2 225 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 225 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 224 280 (Eq.refl Bool.true) (allA_of_3_1 57 224 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 58 223 280 (Eq.refl Bool.true) (allA_succ_of_accept 57 223 280 (Polychromatic418967fa.accept_6_3_1_4_1_25
  57 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 223 280 (accept_3_3 56
  223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 223 280
  (Polychromatic418967fa.accept_16_7_15_8_1_278 55 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 223 280 (Polychromatic418967fa.accept_22_10_3_16_1_15734 54 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 223 280 (accept_3_3 53 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 223 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 223 280 (accept_3_3 50 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 223 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 223 280 (accept_3_3 47 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 223 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 223 280 (accept_3_3 44 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 223 280 (Polychromatic418967fa.accept_23_20_16_4_1_17219 43 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 223 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 280 (accept_3_3 41 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 223 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 280 (accept_3_3 38 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 280 (Polychromatic418967fa.accept_21_16_13_7_1_8385 37 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 280 (Polychromatic418967fa.accept_16_4_15_8_1_2413 36 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 280 (accept_3_3 35 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 223
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 280 (accept_3_3 32 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 280 (accept_3_3 29 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 280 (Polychromatic418967fa.accept_16_12_15_8_1_4586 28 223 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 280 (accept_3_3 26 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 280 (Polychromatic418967fa.accept_16_9_15_8_1_3425 25 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 280 (accept_3_3 23 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 280 (accept_3_3 20 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 280 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 280 (accept_3_3 17 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 223
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 280 (accept_3_3 14 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 280 (accept_3_3 11 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 280 (accept_3_3 8 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 280 (Polychromatic418967fa.accept_16_7_15_8_1_278 7 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 280 (accept_3_3 5 223 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 223 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 280 (accept_3_3 2 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 223 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 222 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 58 222 280 2 29 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 222 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 222 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 222 280 2 28 111 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 222 280
  (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 222 280 2 27 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 222 280 (accept_3_3 53 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 222 280 2 26 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 222 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 222 280 2 25 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 222 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 222 280 2 24 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 222 280 (accept_3_3 47 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 222 280 2 23 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 222 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 222 280 2 22 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 222 280 2 21 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 222 280 (accept_3_3 41 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 222 280 2 20 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 222 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 222 280 2 19 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 222 280
  (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 280 2 18 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 280 (accept_3_3 35 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 222 280 2 17 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 222 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 222 280 2 16 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 280 2 15 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 280 (accept_3_3 29 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 280 2 14 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 222 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 280 2 13 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 280 2 12 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 280 (accept_3_3 23 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 280 2 11 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 222 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 280 2 10 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 280
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 280 2 9 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 280 (accept_3_3 17 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 280 2 8 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 280 2 7 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 280 2 6 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 280 (accept_3_3 11 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 280 2 5 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 280 2 4 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 280 2 3 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 280 (accept_3_3 5 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 280 2 2 111 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 222 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 280 2 1 111 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 280
  (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 222 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 221 280 (Eq.refl
  Bool.true) (allA_of_3_1 60 221 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 220 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 220 280 20 3 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 220 280 (accept_3_3 59 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 220 280 2 29 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 220 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 220 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 220 280 4 14 55 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 220 280 5 11 44 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 220 280 2 27 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 220 280 (accept_3_3 53
  220 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 220 280 4 13 55 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 220 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 220 280 10 5 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 220 280 (Polychromatic418967fa.accept_13_10_12_7_1_1079 49 220 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 220 280 4 12 55 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 220 280 (accept_3_3 47 220 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 220 280 2 23 110 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 220 280 5 9 44 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 220 280 4 11 55 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 220 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 220 280 2 21 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 220 280 (accept_3_3 41 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 220 280 20 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 220 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 220 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 220 280 2 19 110 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 220 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 37 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 220 280 4 9 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 220 280 5 7 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 34 220 280 2 17 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 220 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 220 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 220 280 4 8 55 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 220 280
  (Polychromatic418967fa.accept_13_5_12_7_1_1080 31 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 220 280 10 3 22 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 220 280 (accept_3_3 29 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 220 280 4 7 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 220 280 (Polychromatic418967fa.accept_16_11_12_8_1_1592 27 220 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 220 280 2 13 110 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 220 280 5 5 44 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 220 280 4 6 55 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 280 (accept_3_3 23 220 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 280 2 11 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21
  220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 280 20 1 11 14 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 280
  (Polychromatic418967fa.accept_13_6_12_7_1_5131 19 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 280 2 9 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 280 (accept_3_3 17 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 280 4 4 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 220 280 5 3 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 220 280 2 7 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 220 280 (Polychromatic418967fa.accept_16_13_12_8_1_2451 13 220 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 220 280 4 3 55 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 220 280 (accept_3_3 11 220 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 220 280 10 1 22 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 220 280
  (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 220 280 4 2 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 220 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 220 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 280 2 3 110 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 220 280 5 1 44 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 220 280 4 1 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3
  220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 280 2 1 110 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 280
  (Polychromatic418967fa.accept_16_1_12_8_1_2405 1 220 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 219 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 219 280 (Polychromatic418967fa.accept_9_6_3_1_1_155
  60 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 219 280 (accept_3_3 59
  219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 58 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 219 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 57 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 219 280 (accept_3_3 56 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 219 280 (Polychromatic418967fa.accept_12_6_3_4_1_394
  54 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 280 (accept_3_3 53
  219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 52 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 219 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 280 (accept_3_3 50 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 219 280 (accept_3_3 47 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 219 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 219 280 (Polychromatic418967fa.accept_16_13_11_8_1_2449 45 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 280 (accept_3_3 44 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 219 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 219 280 (accept_3_3 41 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 219 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 219 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 280 (accept_3_3 38 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 219 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 280
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 219 280 (accept_3_3 35 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 219 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 219 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 280 (accept_3_3 32 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 280 (accept_3_3 29 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 280 (accept_3_3 26 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 219 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 280 (accept_3_3 23 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 280 (Polychromatic418967fa.accept_16_5_11_8_1_3431 21 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 280 (accept_3_3 20 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 280 (accept_3_3 17 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 219 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 280 (accept_3_3 14 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 219 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 280
  (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 280 (accept_3_3 11 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 280 (Polychromatic418967fa.accept_17_10_15_8_1_6324 10 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 280 (Polychromatic418967fa.accept_13_9_11_7_1_1077
  9 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 280 (accept_3_3 8
  219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 219 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 280 (accept_3_3 5 219 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 219 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 219 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488
  3 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 280 (accept_3_3 2
  219 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 1 219 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 219 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 218 280 (Eq.refl
  Bool.true) (allA_of_3_1 63 218 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 217 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 217 280 7 9 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 217 280 (accept_3_3 62 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 217 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 217 280 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 217 280 (accept_3_3 59 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 217 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 217
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 217 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 217 280 7 8 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 217 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 217 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 217
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 217 280 (accept_3_3 53 217
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 217 280
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 52 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 217 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 217 280 (accept_3_3 50 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 217 280 7 7 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 217 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 48 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 280 (accept_3_3 47 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 217
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 217 280 (accept_3_3 44 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 217 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 43 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 217 280 7 6 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 217 280 (accept_3_3 41 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 217 280 (Polychromatic418967fa.accept_19_2_8_14_1_3648 40 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 217 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 280 (accept_3_3 38 217 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 217 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 217 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 217 280 7 5 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 217 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 280 (accept_3_3 32 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 280 (accept_3_3 29 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 217 280 7 4 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 217 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 280 (accept_3_3 26
  217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 217 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 280 (accept_3_3 23 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 217 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 217 280 7 3 31 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 217 280 (accept_3_3 20 217 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430
  19 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 280
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 280 (accept_3_3 17 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 280 (Polychromatic418967fa.accept_13_3_9_7_1_1730 16 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 217 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 217 280 7 2 31 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 217 280
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 217 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 217 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 280 (accept_3_3 11 217 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 217 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 280 (accept_3_3 8 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 217
  280 7 1 31 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  217 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 217 280 (accept_3_3 5 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 217 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 4 217 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 280 (accept_3_3 2 217 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 280 (Polychromatic418967fa.accept_15_1_7_10_1_287
  1 217 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 216 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 216 280 8 8 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 216 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 216 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 216 280 2 31 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 216 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073
  61 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 216 280 4 15 54 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 216 280
  (accept_3_3 59 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 216 280 2 29 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 216 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 216 280 8 7 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 216 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 55 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 216 280 2 27 108 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 216 280 (accept_3_3 53 216 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 216 280 4 13 54 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 216 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 216 280 2 25 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 216 280 (Polychromatic418967fa.accept_13_10_8_7_1_1074 49 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 216 280 8 6 27 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 216 280 (accept_3_3 47 216 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 216 280 2 23 108 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 216 280
  (Polychromatic418967fa.accept_21_3_6_7_1_6750 45 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 216 280 4 11 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 216 280 (Polychromatic418967fa.accept_21_1_6_7_1_17183 43 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 216 280 2 21 108 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 216 280 (accept_3_3 41 216 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 216 280 8 5 27 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 216 280
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 216 280 2 19 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 216 280 (Polychromatic418967fa.accept_17_3_12_8_1_1688 37 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 280 4 9 54 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 280 (accept_3_3 35 216 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 280 2 17 108 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 280
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 280 8 4 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 216 280 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 216 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 280 2 15 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 280 (accept_3_3 29 216 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 280 4 7 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 216
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 280 2 13 108 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 25 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 280 8 3 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 280 (accept_3_3 23 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  216 280 2 11 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 216 280 (Polychromatic418967fa.accept_17_4_12_8_1_3833 21 216 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 216 280 4 5 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 280 (Polychromatic418967fa.accept_15_4_6_10_1_823
  19 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 280 2 9 108 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 280
  (accept_3_3 17 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 280 8 2 27 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 280
  (Polychromatic418967fa.accept_13_2_8_7_1_2424 15 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 216 280 2 7 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 216 280 (Polychromatic418967fa.accept_21_13_6_7_1_1237 13 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 280 4 3 54 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 280 (accept_3_3 11 216 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 280 2 5 108 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 280 8 1 27 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 216 280 (Polychromatic418967fa.accept_34_7_12_8_1_17218 7 216 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 280 2 3 108 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 280 (accept_3_3 5 216 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 280 4 1 54 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 216 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 216 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 280 2 1 108 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 280
  (Polychromatic418967fa.accept_13_1_8_7_1_1088 1 216 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 215 280 (Eq.refl
  Bool.true) (allA_of_3_1 66 215 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 214 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 214 280 2 33 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 214 280 (accept_3_3 65 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 214 280 2 32 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 214 280 (Polychromatic418967fa.accept_17_12_10_8_1_5039 63 214 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 214 280 2 31 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 214 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 214 280 2 30 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 214 280 (accept_3_3 59 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 214 280 2 29 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 214 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 57 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 214 280 2 28 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 214 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 214 280 2 27 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 214 280 (accept_3_3 53 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 214 280 2 26 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 214 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 214 280 2 25 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 214 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 49 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 214 280 2 24 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 280 (accept_3_3 47 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 214 280 2 23 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 214 280 (Polychromatic418967fa.accept_21_3_4_7_1_14226 45 214 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 214 280 2 22 107 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 214 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 214 280 2 21 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 214 280 (accept_3_3 41 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 280 2 20 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 280 2 19 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 280 2 18 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 280 (accept_3_3 35 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 280 2 17 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 280 2 16 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 31 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 280 2 15 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 280 (accept_3_3 29 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 280 2 14 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 280 2 13 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 280 2 12 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 280 (accept_3_3 23 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 280 2 11 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 21 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 280 2 10 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 280 2 9 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 280 (accept_3_3 17 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 280 2 8 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 280 2 7 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 280 2 6 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 280 (accept_3_3 11 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 280 2 5 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 280 2 4 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 280 2 3 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 280 (accept_3_3 5 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 280 2 2 107 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 214 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 280 2 1 107 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 214 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 213 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 213 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 66
  213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 213 280 (accept_3_3 65
  213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 213 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 213 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 63 213 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 213 280 (accept_3_3 62 213 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 280
  (Polychromatic418967fa.accept_16_12_5_8_1_2492 60 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 213 280 (accept_3_3 59 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 213 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 213 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 280 (accept_3_3 56 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 280
  (Polychromatic418967fa.accept_11_10_4_5_1_359 54 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 213 280 (accept_3_3 53 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 213 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 213 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 280 (accept_3_3 50 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 213 280 (accept_3_3 47 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 213 280 (Polychromatic418967fa.accept_19_8_4_14_1_5005 46 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 213 280 (Polychromatic418967fa.accept_16_13_5_8_1_5814 45 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 280 (accept_3_3 44 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 213 280 (accept_3_3 41 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 213 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 213 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 280 (accept_3_3 38 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 280
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 213 280 (accept_3_3 35 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 213 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 213 280 (Polychromatic418967fa.accept_17_16_9_8_1_5063 33 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 280 (accept_3_3 32 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 213 280 (accept_3_3 29 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 213 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 213 280 (Polychromatic418967fa.accept_16_11_5_8_1_2427 27 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 280 (accept_3_3 26 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 280
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 24 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 213 280 (accept_3_3 23 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 213 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 213 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 280 (accept_3_3 20 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 213 280 (accept_3_3 17 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 213 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 213 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 280 (accept_3_3 14 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 280 (accept_3_3 11 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 280 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 280 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 280 (accept_3_3 8 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 213 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 280 (accept_3_3 5 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 213 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 280 (accept_3_3 2 213 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 212 280 (Eq.refl Bool.true)
  (allA_of_3_1 69 212 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 211 280 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 211 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 211 280 (accept_3_3 68 211 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 211 280 (Polychromatic418967fa.accept_15_7_1_10_1_305 67 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 211 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 211 280 (accept_3_3 65 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 211 280 (Polychromatic418967fa.accept_19_7_2_14_1_3569 64 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 211 280 (accept_3_3 62 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 211 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 211 280 (accept_3_3 59 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 211 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 211 280 (accept_3_3 56 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 211 280 (Polychromatic418967fa.accept_17_4_7_8_1_7491 55 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 211 280
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 211 280 (accept_3_3 53 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 280 (accept_3_3 50 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 211 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 211 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 280 (accept_3_3 47 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 280 (accept_3_3 44 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 280 (accept_3_3 41 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 40 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 280 (accept_3_3 38 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 211 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 280
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 36 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 280 (accept_3_3 35 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 280 (accept_3_3 32 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 280 (Polychromatic418967fa.accept_17_14_7_8_1_7544 31 211 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 280 (accept_3_3 29 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 280 (accept_3_3 26 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 280 (accept_3_3 23 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 280 (accept_3_3 20 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 280
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 280 (accept_3_3 17 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 280 (accept_3_3 14 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 211 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 280 (accept_3_3 11 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 280 (accept_3_3 8 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 280 (accept_3_3 5 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 4 211 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 280 (accept_3_3 2 211 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 211 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 210 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 210 280 70 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 210 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 210 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 210 280 2 34 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 210 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 67
  210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 210 280 2 33 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 210 280 5 13 42
  56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 210 280 2 32
  105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 210 280 7
  9 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 210 280 2
  31 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 210
  280 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 210 280 10 6 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 210 280 (accept_3_3 59 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 210 280 2 29 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 210 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 210 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 210 280 14 4 15 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 210 280 5 11 42 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 210 280 2 27 105 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 210 280 (accept_3_3 53
  210 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 210 280 2 26 105 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 210 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 210 280 10 5 21 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 210 280 7 7 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 210 280 2 24 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 210 280 (accept_3_3 47 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 210 280 2 23 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 210 280 5 9 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 210 280 2 22 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 210 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 210 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 210 280 14 3 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 210 280 (accept_3_3 41 210 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 280 10 4 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 280
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 210 280 2 19 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 210 280 (Polychromatic418967fa.accept_19_18_1_14_1_4978 37 210 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 280 2 18 105 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 210 280 35 1 6 8 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 210 280 2 17 105 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 280 2 16 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 210 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 210 280 10 3 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 210 280 (accept_3_3 29 210 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 280 14 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 280 (Polychromatic418967fa.accept_12_3_6_4_1_400
  27 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 280 2 13 105 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 210 280 5 5 42 56
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 210 280 2 12 105
  140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 280
  (accept_3_3 23 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 280 2 11 105 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 280 7 3 30 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 280 10 2 21 28
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 280
  (Polychromatic418967fa.accept_22_19_12_16_1_6241 19 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 210 280 2 9 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 210 280 (accept_3_3 17 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 280 2 8 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 210 280 5 3 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 210 280 14 1 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 210 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 210 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 280 2 6 105 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 280 (accept_3_3 11 210 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 280 10 1 21 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 280 2 4 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 210 280 7 1 30 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 210 280 2 3 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 5 210 280 5 1 42 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 4 210 280 2 2 105 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 210 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 280 2 1 105 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 280
  (Polychromatic418967fa.accept_22_1_12_16_1_6178 1 210 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 209 280
  (Eq.refl Bool.true) (allA_of_3_1 72 209 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 208 280 (Eq.refl
  Bool.true) (allA_succ_of_gcd 72 208 280 8 9 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 208 280 (accept_3_3 71 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 208 280 2 35 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 208 280 (Polychromatic418967fa.accept_17_1_4_8_1_5049 69 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 208 280 4 17 52 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 208 280
  (Polychromatic418967fa.accept_19_10_18_14_1_7867 67 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 208 280 2 33 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 208 280 (accept_3_3 65 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 208 280 8 8 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 208 280 (Polychromatic418967fa.accept_15_3_13_10_1_2332 63 208 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 208 280 2 31 104 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 208 280
  (Polychromatic418967fa.accept_11_6_10_5_1_341 61 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 208 280 4 15 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 208 280 (accept_3_3 59 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 208 280 2 29 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 208 280 (Polychromatic418967fa.accept_15_12_13_10_1_812 57 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 208 280 8 7 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 208 280
  (Polychromatic418967fa.accept_21_13_19_7_1_5162 55 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 208 280 2 27 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 208 280 (accept_3_3 53 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 208 280 4 13 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 208 280 (Polychromatic418967fa.accept_19_13_18_14_1_3522 51 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 208 280 2 25 104 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 208 280
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 208 280 8 6 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 208 280 (accept_3_3 47 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 208 280 2 23 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 208 280 (Polychromatic418967fa.accept_19_7_18_14_1_9185 45 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 208 280 4 11 52 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 208 280
  (Polychromatic418967fa.accept_21_1_19_7_1_1218 43 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 208 280 2 21 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 208 280 (accept_3_3 41 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 208 280 8 5 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 208 280 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 208 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 280 2 19 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202
  37 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 208 280 4 9 52 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 208 280
  (accept_3_3 35 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 208 280 2 17 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 208 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 33 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 208 280 8 4 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 208 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 208 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 208 280 2 15 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 208 280 (accept_3_3 29
  208 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 208 280 4 7 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 208 280
  (Polychromatic418967fa.accept_15_12_13_10_1_812 27 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 208 280 2 13 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 208 280 (Polychromatic418967fa.accept_21_4_19_7_1_5142 25 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 208 280 8 3 26 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 280 (accept_3_3 23 208 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 280 2 11 104 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 280
  (Polychromatic418967fa.accept_23_21_1_4_1_5657 21 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 208 280 4 5 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 208 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 208 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 208 280 2 9 104 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 208 280 (accept_3_3 17 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 208 280 8 2 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 208 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202
  15 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 280 2 7 104 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 280
  (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 280 4 3 52 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 208 280 (accept_3_3 11 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  208 280 2 5 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 208 280 (Polychromatic418967fa.accept_21_9_19_7_1_8376 9 208 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 280 8 1 26 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 280 (Polychromatic418967fa.accept_17_7_4_8_1_7678 7 208 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 280 2 3 104 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 280 (accept_3_3 5
  208 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 280 4 1 52 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 280
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 208 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 280 2 1 104 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 280 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 208 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 207 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 207 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 207 280
  (Polychromatic418967fa.accept_19_15_17_14_1_1370 72 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 207 280 (accept_3_3 71 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 207 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 70 207 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 69 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 207 280 (accept_3_3 68 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  67 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 207 280 (accept_3_3 65 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 207 280 (Polychromatic418967fa.accept_17_13_3_8_1_6310 64 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 207 280 (Polychromatic418967fa.accept_13_11_12_7_1_2443 63 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 207 280 (accept_3_3 62 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 280
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 60 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 207 280 (accept_3_3 59 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 207 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 58 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 207 280 (Polychromatic418967fa.accept_13_5_12_7_1_1080 57 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 280 (accept_3_3 56 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 207 280 (accept_3_3 53 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 207 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 52 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 207 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 51 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 280 (accept_3_3 50 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 280
  (Polychromatic418967fa.accept_18_12_9_10_1_3104 48 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 207 280 (accept_3_3 47 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 280 (Polychromatic418967fa.accept_17_12_3_8_1_7627 46 207 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 280 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 280 (accept_3_3 44 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 280 (accept_3_3 41 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 40 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 39 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 280 (accept_3_3 38 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 280
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 280 (accept_3_3 35 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 280 (Polychromatic418967fa.accept_13_8_12_7_1_2442 34 207 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 280 (Polychromatic418967fa.accept_16_1_15_8_1_2411 33 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 280 (accept_3_3 32 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 280 (accept_3_3 29 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 280 (Polychromatic418967fa.accept_15_13_12_10_1_4352 28 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 280 (Polychromatic418967fa.accept_21_6_18_7_1_3764 27 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 280 (accept_3_3 26 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25
  207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 280
  (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 280 (accept_3_3 23 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 207 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 280
  (Polychromatic418967fa.accept_13_8_12_7_1_2442 21 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 207 280 (accept_3_3 20 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 207 280 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 280 (accept_3_3 17 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 280 (Polychromatic418967fa.accept_19_16_17_14_1_4969 16
  207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 280
  (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 280 (accept_3_3 14 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 280 (Polychromatic418967fa.accept_16_12_15_8_1_4586 12 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 280 (accept_3_3 11 207
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 280
  (Polychromatic418967fa.accept_13_10_12_7_1_1079 10 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 280 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 280 (accept_3_3 8 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 280 (accept_3_3 5 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 280 (Polychromatic418967fa.accept_13_4_12_7_1_2439 4 207 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 280 (Polychromatic418967fa.accept_19_3_17_14_1_2354 3 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 280 (accept_3_3 2 207 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 206 280 (Eq.refl
  Bool.true) (allA_of_3_1 75 206 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 205 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 205 280 5 15 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 205 280 (accept_3_3 74 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 205 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 205 280 (Polychromatic418967fa.accept_17_4_1_8_1_5070 72 205
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 205 280 (accept_3_3 71 205
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 205 280 5 14 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 205 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 205 280 (accept_3_3 68 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 205 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 66 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 205 280 5 13 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 205 280
  (Polychromatic418967fa.accept_11_9_7_5_1_749 64 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 205 280 (accept_3_3 62 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 205 280 (Polychromatic418967fa.accept_19_4_15_14_1_10614 61 205 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 205 280 5 12 41 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 205 280 (accept_3_3 59 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  58 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 205 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 205 280 (accept_3_3 56 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  205 280 5 11 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 205 280 (Polychromatic418967fa.accept_21_12_16_7_1_14243 54 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 280 (accept_3_3 53 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 52 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 205 280 5 10 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 280 (Polychromatic418967fa.accept_9_3_7_1_1_143
  48 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 280 (accept_3_3 47
  205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 280
  (Polychromatic418967fa.accept_12_10_1_4_1_392 46 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 205 280 5 9 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 205 280 (accept_3_3 44 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 205 280 (Polychromatic418967fa.accept_13_4_10_7_1_1701 43 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 280 (accept_3_3 41 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 205 280 5 8 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 280 (accept_3_3 38 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 280
  (Polychromatic418967fa.accept_16_5_13_8_1_2454 37 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 205 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 205 280 5 7 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 205 280 (Polychromatic418967fa.accept_12_10_1_4_1_392
  34 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 280 (accept_3_3 32 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 205 280 5 6 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 205 280 (accept_3_3 29 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 205 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 28 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27
  205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 280 (accept_3_3 26
  205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 205 280 5 5 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 205 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 280 (accept_3_3 23 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 205 280 5 4 41 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 205 280
  (Polychromatic418967fa.accept_16_3_13_8_1_1594 19 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 205 280 (Polychromatic418967fa.accept_19_18_15_14_1_5017 18 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 280 (accept_3_3 17 205 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 16 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 205 280 5 3 41 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 205 280 (accept_3_3 14
  205 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 205 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 280 (accept_3_3 11 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 205 280 5 2 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 280 (accept_3_3 8 205 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 280 (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 205 280 5 1 41 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 205 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 205 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 280 (accept_3_3 2 205 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 280
  (Polychromatic418967fa.accept_19_1_15_14_1_5032 1 205 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 205 280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 204 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 204 280 4 19 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 204 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 204 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 204 280 2 37 102 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 204 280
  (Polychromatic418967fa.accept_13_8_9_7_1_530 73 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 204 280 4 18 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 204 280 (accept_3_3 71 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 204 280 2 35 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 204 280 (Polychromatic418967fa.accept_13_4_9_7_1_2402 69 204 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 204 280 4 17 51 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 204 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 204 280 2 33 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 280 (accept_3_3 65 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 204 280 4 16 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 204 280 (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 204 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 204 280 2 31 102 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 280 4 15 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 280 (accept_3_3 59 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 204 280 2 29 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 204 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 204 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 204 280 4 14 51 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 280
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 55 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 280 2 27 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 280 (accept_3_3 53 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 204 280 4 13 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 204 280 (Polychromatic418967fa.accept_16_3_12_8_1_808 51 204 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 204 280 2 25 102 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 280 4 12 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 280 (accept_3_3 47 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 280 2 23 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 204 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 204 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 204 280 4 11 51 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 280 2 21 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 280 (accept_3_3 41 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 204 280 4 10 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 204 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 204 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 204 280 2 19 102 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 280
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 37 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 280 4 9 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 280 (accept_3_3 35 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  204 280 2 17 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 204 280 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 204 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 280 4 8 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 31
  204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 280 2 15 102 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 280
  (accept_3_3 29 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 280 4 7 51 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 204 280 2 13 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 204 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 204 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 280 4 6 51 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 280 (accept_3_3 23 204 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 280 2 11 102 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 280 4 5 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 280 (Polychromatic418967fa.accept_13_6_9_7_1_2430 19 204 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 280 2 9 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 280 (accept_3_3 17 204 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 280 4 4 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 280 (Polychromatic418967fa.accept_13_2_9_7_1_164 15 204 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 280 2 7 102 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 280 4 3 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 280 (accept_3_3 11 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  204 280 2 5 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 204 280 (Polychromatic418967fa.accept_16_9_12_8_1_1554 9 204 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 280 4 2 51 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 280 2 3 102 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 280 (accept_3_3 5
  204 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 280 4 1 51 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 204 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 280 2 1 102 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 204 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 203 280 (Eq.refl
  Bool.true) (allA_of_3_1 78 203 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 202 280 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 202 280 2 39 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 202 280 (accept_3_3 77 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 202 280 2 38 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 202 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 75 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 202 280 2 37 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 202 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 202 280 2 36 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 202 280 (accept_3_3 71 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 202 280 2 35 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 202 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 69 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 202 280 2 34 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 202 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 202 280 2 33 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 202 280 (accept_3_3 65 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 202 280 2 32 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 202 280 (Polychromatic418967fa.accept_15_3_7_10_1_2324 63 202 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 202 280 2 31 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 202 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 61 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 202 280 2 30 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 202 280 (accept_3_3 59 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 202 280 2 29 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 202 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 57 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 202 280 2 28 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 202 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 55 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 202 280 2 27 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 202 280 (accept_3_3 53 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 202 280 2 26 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 202 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 51 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 280 2 25 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 202 280 2 24 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 202 280 (accept_3_3 47 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 280 2 23 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 280 (Polychromatic418967fa.accept_19_7_12_14_1_9206 45 202 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 280 2 22 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 43 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 280 2 21 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 280 (accept_3_3 41 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 280 2 20 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 39 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 280 2 19 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 280 2 18 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 280 (accept_3_3 35 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 280 2 17 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 280 2 16 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 280 2 15 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 280 (accept_3_3 29 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 280 2 14 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 280 (Polychromatic418967fa.accept_15_12_7_10_1_3297 27 202 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 280 2 13 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 25 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 280 2 12 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 280 (accept_3_3 23 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 280 2 11 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 280 2 10 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 280 2 9 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 280 (accept_3_3 17 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 280 2 8 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 280 (Polychromatic418967fa.accept_9_6_4_1_1_390 15 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 280 2 7 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 280 2 6 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 280 (accept_3_3 11 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 280 2 5 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 280 (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 202 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 280 2 4 101 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 280
  (Polychromatic418967fa.accept_9_7_4_1_1_391 7 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 280 2 3 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 280 (accept_3_3 5 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 280 2 2 101 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 280 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 202 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 280 2 1 101 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 202 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 201
  280 (Eq.refl Bool.true) (allA_succ_of_accept 79 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 201 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 201 280 (accept_3_3 77 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 201 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 201 280 (Polychromatic418967fa.accept_17_7_14_8_1_5069 75 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 201 280 (accept_3_3 74 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 201 280
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 72 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 201 280 (accept_3_3 71 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 201 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 201 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 280 (accept_3_3 68 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 201 280 (accept_3_3 65 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 201 280 (Polychromatic418967fa.accept_13_12_6_7_1_1071 64 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 201 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 280 (accept_3_3 62 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 201 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 201 280 (accept_3_3 59 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 201 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 201 280 (Polychromatic418967fa.accept_15_12_6_10_1_1516 57 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 280 (accept_3_3 56 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 201 280 (accept_3_3 53 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 201 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 201 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 280 (accept_3_3 50 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 201 280
  (Polychromatic418967fa.accept_13_9_6_7_1_551 48 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 201 280 (accept_3_3 47 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 201 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 201 280 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 280 (accept_3_3 44 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 201 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 201 280 (accept_3_3 41 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 201 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 201 280 (Polychromatic418967fa.accept_16_7_9_8_1_829 39 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 280 (accept_3_3 38 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 201 280
  (Polychromatic418967fa.accept_16_4_9_8_1_2509 36 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 201 280 (accept_3_3 35 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 201 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 201 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 280 (accept_3_3 32 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 280
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 201 280 (accept_3_3 29 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 201 280 (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 201 280 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 280 (accept_3_3 26 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 201 280 (accept_3_3 23 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 201 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 201 280 (Polychromatic418967fa.accept_23_21_17_4_1_17217 21 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 280 (accept_3_3 20 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 201 280 (accept_3_3 17 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 201 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 280 (accept_3_3 14 201 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 280
  (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 280 (accept_3_3 11 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 201 280 (Polychromatic418967fa.accept_22_10_3_16_1_15734 10 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 280 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 280 (accept_3_3 8 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 280 (accept_3_3 5 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 201 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 280 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 280 (accept_3_3 2 201 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 200 280 (Eq.refl
  Bool.true) (allA_of_3_1 81 200 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 199 280 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 199 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 199 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 199 280 (accept_3_3 80 199 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 199 280 (Polychromatic418967fa.accept_16_15_7_8_1_8189 79 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 199 280
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 78 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 199 280 (accept_3_3 77 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 199 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 76 199 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 199 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 199 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 199 280 (accept_3_3 74 199 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 199 280
  (Polychromatic418967fa.accept_15_13_4_10_1_821 73 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 199 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 199 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 199 280 (accept_3_3 71 199 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 199 280 (accept_3_3 68 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 199 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 67 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 199 280 (Polychromatic418967fa.accept_15_6_4_10_1_2319 66 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 199 280 (accept_3_3 65 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 199 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 64 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 199 280 (accept_3_3 62 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 199 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 199 280 (Polychromatic418967fa.accept_16_12_7_8_1_1589 60 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 199 280 (accept_3_3 59 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 199 280 (accept_3_3 56 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 199 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 199 280 (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 199 280 (accept_3_3 53 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 199 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 199 280 (accept_3_3 50 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 199 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 49 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 199 280 (Polychromatic418967fa.accept_13_9_4_7_1_1694 48 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 199 280 (accept_3_3 47 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 199 280 (accept_3_3 44 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 199 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 199 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 199 280 (accept_3_3 41 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 199 280 (Polychromatic418967fa.accept_21_19_10_7_1_8384 40 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 199 280 (accept_3_3 38 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 199 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 37 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 199 280 (Polychromatic418967fa.accept_13_10_4_7_1_2465 36 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 199 280 (accept_3_3 35 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 199 280 (accept_3_3 32 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 199 280 (Polychromatic418967fa.accept_16_15_7_8_1_8189 31 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 199 280 (Polychromatic418967fa.accept_19_11_9_14_1_6386 30 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 199 280 (accept_3_3 29 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 199 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 199 280 (accept_3_3 26 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 199 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 25 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 199 280 (Polychromatic418967fa.accept_13_11_4_7_1_2419 24 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 199 280 (accept_3_3 23 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 280 (accept_3_3 20 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 280 (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 280 (Polychromatic418967fa.accept_21_18_10_7_1_14209 18 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 280 (accept_3_3 17 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 280 (Polychromatic418967fa.accept_13_3_4_7_1_1711 16 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 280 (accept_3_3 14 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 280 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 280 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 280 (accept_3_3 11 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 199
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 280 (accept_3_3 8 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 280 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 280 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 199 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 280 (accept_3_3 5 199 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 280 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 199 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 280
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 280 (accept_3_3 2 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 280 (Polychromatic418967fa.accept_16_1_7_8_1_3422 1 199 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 198 280 (Eq.refl Bool.true) (allA_succ_of_gcd 82 198 280 2 41 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 81 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 198 280 2 40 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 198 280 (Polychromatic418967fa.accept_13_1_3_7_1_1710 79 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 198 280 2 39 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 198 280 (accept_3_3 77 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 198 280 2 38 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 75 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 198 280 2 37 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 198 280 (Polychromatic418967fa.accept_13_8_3_7_1_2455 73 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 198 280 2 36 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 198 280 (accept_3_3 71 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 280 2 35 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 69 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 198 280 2 34 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 198 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 67 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 198 280 2 33 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 198 280 (accept_3_3 65 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 280 2 32 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 63 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 198 280 2 31 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 198 280 (Polychromatic418967fa.accept_13_9_3_7_1_1065 61 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 198 280 2 30 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 198 280 (accept_3_3 59 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 280 2 29 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 57 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 198 280 2 28 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 198 280 (Polychromatic418967fa.accept_21_13_9_7_1_9858 55 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 198 280 2 27 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 198 280 (accept_3_3 53 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 280 2 26 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 280 2 25 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 280 (Polychromatic418967fa.accept_13_10_3_7_1_2517 49 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 198 280 2 24 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 198 280 (accept_3_3 47 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 280 2 23 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 45 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 280 2 22 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 280 (Polychromatic418967fa.accept_13_4_3_7_1_2515 43 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 198 280 2 21 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 198 280 (accept_3_3 41 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 280 2 20 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 39 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 280 2 19 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 280 (Polychromatic418967fa.accept_13_11_3_7_1_2513 37 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 198 280 2 18 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 198 280 (accept_3_3 35 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 280 2 17 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 33 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 280 2 16 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 280 (Polychromatic418967fa.accept_17_14_11_8_1_3854 31 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 280 2 15 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 280 (accept_3_3 29 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 280 2 14 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 27 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 280 2 13 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 280 (Polychromatic418967fa.accept_19_6_8_14_1_2351 25 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 280 2 12 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 280 (accept_3_3 23 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 280 2 11 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 280 2 10 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 280 (Polychromatic418967fa.accept_17_2_11_8_1_2726 19 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 198 280 2 9 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 198 280 (accept_3_3 17 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 280 2 8 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 280
  (Polychromatic418967fa.accept_12_3_6_4_1_400 15 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 280 2 7 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 280 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 198 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 280 2 6 99 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 280 (accept_3_3 11 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 280 2 5 99 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 280
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 280 2 4 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 280 (Polychromatic418967fa.accept_15_7_3_10_1_817 7 198 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 280 2 3 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 280 (accept_3_3 5 198 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 280 2 2 99 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 198 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 198 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 280 2 1 99 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 280
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 1 198 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84
  197 280 (Eq.refl Bool.true) (allA_of_3_1 84 197 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 196 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 196 280 28 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 196 280 (accept_3_3 83 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 196 280 2 41 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 196 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 196 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 196 280 4 20 49 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 196 280
  (Polychromatic418967fa.accept_16_15_4_8_1_1562 79 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 196 280 2 39 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 196 280 7 11 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 196 280 4 19 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 196 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 196 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 196 280 2 37 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 196 280
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 196 280 4 18 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 196 280 (accept_3_3 71 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 196 280 14 5 14 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 196 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 196 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 196 280 4 17 49 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 196 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 67 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 196 280 2 33 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 196 280 (accept_3_3 65 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 196 280 4 16 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 196 280 7 9 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 62 196 280 2 31 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 196 280 (Polychromatic418967fa.accept_16_13_4_8_1_4557 61 196 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 196 280 4 15 49 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 196 280 (accept_3_3 59 196 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 196 280 2 29 98 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 196 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 196 280 28 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 196 280 (Polychromatic418967fa.accept_13_3_1_7_1_1706 55 196 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 196 280 2 27 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 196 280 (accept_3_3 53 196 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 196 280 4 13 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 196 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 196 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 196 280 2 25 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 49 196 280 7 7 28 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 48 196 280 4 12 49 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 196 280
  (accept_3_3 47 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 196 280 2 23 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 196 280
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 196 280 4 11 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 196 280 (Polychromatic418967fa.accept_15_13_1_10_1_816 43 196 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 196 280 14 3 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 196 280 (accept_3_3 41 196 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 196 280 4 10 49 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 196 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 196 280 2 19 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 196 280 (Polychromatic418967fa.accept_13_11_1_7_1_1691 37 196 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 196 280 4 9 49 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 196 280 7 5 28 40 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 196 280 2 17 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 196 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 196 280 4 8 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 196 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 196 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 280 2 15 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 280 (accept_3_3 29 196 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 280 28 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 280 (Polychromatic418967fa.accept_16_11_4_8_1_3435 27 196
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 196 280 2 13 98 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 196 280
  (Polychromatic418967fa.accept_16_9_4_8_1_2533 25 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 196 280 4 6 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 196 280 (accept_3_3 23 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  196 280 2 11 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  21 196 280 7 3 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  20 196 280 4 5 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 280 (Polychromatic418967fa.accept_13_6_1_7_1_1690 19 196 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 280 2 9 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 280 (accept_3_3 17 196 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 280 4 4 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 280 (Polychromatic418967fa.accept_9_6_7_1_1_145 15 196 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 280 14 1 14 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 280
  (Polychromatic418967fa.accept_9_4_7_1_1_379 13 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 280 4 3 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 196 280 (accept_3_3 11 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  196 280 2 5 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 196 280 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 196 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 280 4 2 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 196 280 7 1 28 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 196 280 2 3 98 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 280 (accept_3_3 5 196 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 196 280 4 1 49 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 196 280 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 196 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 196 280 2 1 98 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 280
  (Polychromatic418967fa.accept_16_1_4_8_1_3434 1 196 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86
  195 280 (Eq.refl Bool.true) (allA_succ_of_gcd 85 195 280 5 17 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 195 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 84 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 195 280 (accept_3_3 83 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 195 280
  (Polychromatic418967fa.accept_19_6_5_14_1_3582 82 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 195 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 81 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 195 280 5 16 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79
  195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 195 280
  (Polychromatic418967fa.accept_12_6_3_4_1_394 78 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 195 280 (accept_3_3 77 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 195 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 75 195 280 5 15 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 195 280 (accept_3_3 74 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 195 280 (Polychromatic418967fa.accept_21_9_6_7_1_6749 72 195
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 280 (accept_3_3 71 195
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 195 280 5 14 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 195 280
  (Polychromatic418967fa.accept_11_3_8_5_1_336 69 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 195 280 (accept_3_3 68 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 195 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 195 280 5 13 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 195 280
  (Polychromatic418967fa.accept_21_1_6_7_1_17183 64 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 195 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 63 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 280 (accept_3_3 62 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 195 280 5 12 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 195 280 (accept_3_3 59 195 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 195 280 (accept_3_3 56 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  195 280 5 11 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 195 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 54 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 280 (accept_3_3 53 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 195 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 280
  (Polychromatic418967fa.accept_19_13_5_14_1_3530 51 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 195 280 5 10 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 195 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 195 280 (accept_3_3 47 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 195 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 195 280 5 9 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 195 280 (accept_3_3 44 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 195
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 280 (accept_3_3 41 195
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 195 280 5 8 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 195 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 195 280 (accept_3_3 38 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 195 280 (Polychromatic418967fa.accept_11_3_8_5_1_336 36 195 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 195 280 5 7 39 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 195 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 34 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 195 280 (Polychromatic418967fa.accept_21_12_6_7_1_3739 33 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 280 (accept_3_3 32 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 280 5 6 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 280 (accept_3_3 29 195 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 280 (Polychromatic418967fa.accept_16_12_3_8_1_5729 28 195
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 280
  (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 280 (accept_3_3 26 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  195 280 5 5 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 195 280 (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 280 (accept_3_3 23 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 280 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 195 280 5 4 39 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 195 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 195 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 280 (accept_3_3 17 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 195 280 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 280 5 3 39 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 280 (accept_3_3 14 195 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 280
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 280 (accept_3_3 11 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  195 280 5 2 39 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 195 280 (Polychromatic418967fa.accept_18_9_15_10_1_395 9 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 280 (accept_3_3 8 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 280 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 195 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 280 5 1 39 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 4 195 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 195 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 280 (accept_3_3 2 195 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 195 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 195 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 194 280
  (Eq.refl Bool.true) (allA_of_3_1 87 194 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 193 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 193 280 (accept_3_3 86 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 193 280 (Polychromatic418967fa.accept_19_9_3_14_1_2400 85 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 193 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 193 280 (accept_3_3 83 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 193 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 82 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 193 280 (accept_3_3 80 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 79 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 193 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 193 280 (accept_3_3 77 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 193 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 76 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 280 (accept_3_3 74 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 193 280 (Polychromatic418967fa.accept_16_9_1_8_1_5766 73 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 193 280
  (Polychromatic418967fa.accept_15_12_13_10_1_812 72 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 193 280 (accept_3_3 71 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 193 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 280 (accept_3_3 68 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 193 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732
  67 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 193 280 (accept_3_3 65 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 193 280 (Polychromatic418967fa.accept_13_12_11_7_1_2491 64 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 280 (accept_3_3 62 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 280 (accept_3_3 59 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 280 (accept_3_3 56 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 280 (Polychromatic418967fa.accept_13_3_11_7_1_2488 55 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 280
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 54 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 280 (accept_3_3 53 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 280 (accept_3_3 50 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 280 (accept_3_3 47 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 280 (accept_3_3 44 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 280 (accept_3_3 41 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 280 (Polychromatic418967fa.accept_13_1_11_7_1_1704 40 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 280 (accept_3_3 38 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 280 (Polychromatic418967fa.accept_18_1_13_10_1_2024 37 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 280
  (Polychromatic418967fa.accept_16_4_1_8_1_835 36 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 280 (accept_3_3 35 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 280 (accept_3_3 32 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 280 (Polychromatic418967fa.accept_13_5_11_7_1_559 31 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 280 (accept_3_3 29 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 280 (Polychromatic418967fa.accept_16_12_1_8_1_5767 28 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 280 (accept_3_3 26 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 280 (accept_3_3 23 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 280 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 280 (accept_3_3 20 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 280 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 280
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 280 (accept_3_3 17 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 280 (accept_3_3 14 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 280 (Polychromatic418967fa.accept_21_13_4_7_1_5190 13 193 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 280
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 280 (accept_3_3 11 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 280 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 280 (accept_3_3 8 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 280 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 280
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 280 (accept_3_3 5 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 280 (Polychromatic418967fa.accept_13_4_11_7_1_558 4 193 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 280 (accept_3_3 2 193 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 280 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 193 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 192 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 192 280 8 11 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 192 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 87 192 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 192 280 2 43 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 192 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 85 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 192 280 4 21 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 192 280 (accept_3_3 83 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 192 280 2 41 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 192 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 81 192 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 192 280 8 10 24 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 192 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 79 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 280 2 39 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 280 (accept_3_3 77 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 192 280 4 19 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 192 280 (Polychromatic418967fa.accept_21_12_3_7_1_14223 75 192 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 192 280 2 37 96 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 192 280
  (Polychromatic418967fa.accept_13_8_10_7_1_1702 73 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 280 8 9 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 192 280 (accept_3_3 71 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  192 280 2 35 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 192 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 192 280 4 17 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 192 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 67
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 192 280 2 33 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 192 280 (accept_3_3 65
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 192 280 8 8 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 192 280
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 63 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 192 280 2 31 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 192 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 192 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 192 280 4 15 48 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 280 (accept_3_3 59 192 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 280 2 29 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 280 (Polychromatic418967fa.accept_21_15_3_7_1_6748
  57 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 192 280 8 7 24 35
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 280
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 55 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 280 2 27 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 280 (accept_3_3 53 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 192 280 4 13 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 192 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 192 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 192 280 2 25 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 192 280
  (Polychromatic418967fa.accept_9_4_3_1_1_154 49 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 280 8 6 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 192 280 (accept_3_3 47 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  192 280 2 23 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 192 280 (Polychromatic418967fa.accept_18_9_12_10_1_387 45 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 192 280 4 11 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 192 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 43
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 192 280 2 21 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 192 280 (accept_3_3 41
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 280 8 5 24 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 280 2 19 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 280 (Polychromatic418967fa.accept_15_7_12_10_1_4335 37 192 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 280 4 9 48 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 280 (accept_3_3 35 192 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 280 2 17 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 280
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 280 8 4 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 192 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 280 2 15 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 280 (accept_3_3 29 192 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 280 4 7 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 280 (Polychromatic418967fa.accept_18_9_12_10_1_387 27 192
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 280 2 13 96 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 280
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 280 8 3 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 192 280 (accept_3_3 23 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  192 280 2 11 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 192 280 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 280 4 5 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 280
  (Polychromatic418967fa.accept_23_19_8_4_1_17216 19 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 192 280 2 9 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 192 280 (accept_3_3 17 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 280 8 2 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 192 280 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 280 2 7 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 280 (Polychromatic418967fa.accept_9_4_3_1_1_154 13
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 280 4 3 48 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 280 (accept_3_3 11
  192 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 280 2 5 96 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 280
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 280 8 1 24 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 280 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 280 2 3 96 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 280 (accept_3_3 5 192 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 280 4 1 48 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 280 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 192 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 280 2 1 96 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 280
  (Polychromatic418967fa.accept_19_1_2_14_1_3666 1 192 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  90 191 280 (Eq.refl Bool.true) (allA_of_3_1 90 191 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 190 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 190 280 10 9 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 190 280 (accept_3_3 89 190 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 190 280 2 44 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 190 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 87 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 190 280 2 43 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 190 280 5 17 38 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 190 280 2 42 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 190 280
  (accept_3_3 83 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 190 280 2 41 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 190 280
  (Polychromatic418967fa.accept_13_3_8_7_1_4135 81 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 190 280 10 8 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 190 280 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 190 280 2 39 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 190 280 (accept_3_3 77 190 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 190 280 2 38 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 190 280 5 15 38 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 190 280 2 37 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 190 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 190 280 2 36 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 190 280 (accept_3_3 71 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 190 280 10 7 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 190 280 (Polychromatic418967fa.accept_21_6_1_7_1_11405 69 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 190 280 2 34 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 190 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 190 280 2 33 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 190 280 5 13 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 190 280 2 32 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 190 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 190 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 190 280 2 31 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 190 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 190 280 10 6 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 190 280 (accept_3_3 59 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 190 280 2 29 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 190 280 (Polychromatic418967fa.accept_21_15_1_7_1_6723 57 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 190 280 2 28 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 190 280 5 11 38 56 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 190 280 2 27 95 140
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 190 280
  (accept_3_3 53 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 190 280 2 26 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 190 280
  (Polychromatic418967fa.accept_13_12_8_7_1_2526 51 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 190 280 10 5 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 190 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 190 280 2 24 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 190 280 (accept_3_3 47 190 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 190 280 2 23 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 190 280 5 9 38 56 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 190 280 2 22 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 190 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 43 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 190 280 2 21 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 190 280 (accept_3_3 41 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 190 280 10 4 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 190 280 (Polychromatic418967fa.accept_17_5_3_8_1_1697 39 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 190 280 2 19 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 190 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 190 280 2 18 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 190 280 5 7 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 190 280 2 17 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 190 280 (Polychromatic418967fa.accept_21_12_1_7_1_17173 33 190 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 190 280 2 16 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 190 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 190 280 10 3 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 190 280 (accept_3_3 29 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 190 280 2 14 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 190 280 (Polychromatic418967fa.accept_13_1_8_7_1_1088 27 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 190 280 2 13 95 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 190 280 5 5 38 56 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 190 280 2 12 95 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 190 280 (accept_3_3 23
  190 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 190 280 2 11 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 190 280
  (Polychromatic418967fa.accept_23_21_6_4_1_7326 21 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 190 280 10 2 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 190 280 (Polychromatic418967fa.accept_11_8_3_5_1_355 19 190 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 190 280 2 9 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 190 280 (accept_3_3 17 190 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 190 280 2 8 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 190 280 5 3 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 190 280 2 7 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 280
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 280 2 6 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 280 (accept_3_3 11 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 280 10 1 19 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 280 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 190 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 280 2 4 95 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 280
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 280 2 3 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 190 280 5 1 38 56 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 190 280 2 2 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 190 280 (Polychromatic418967fa.accept_13_3_8_7_1_4135 3 190 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 190 280 2 1 95 140 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 280 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  190 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190
  280))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 189 280
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 189 280 7 13 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 189 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 90 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 189 280 (accept_3_3 89 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 280
  (Polychromatic418967fa.accept_23_19_5_4_1_12535 88 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 189 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 87 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 189 280 (accept_3_3 86 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 189 280 7 12 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 189 280 (accept_3_3 83
  189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 280
  (Polychromatic418967fa.accept_25_7_14_5_1_17215 82 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 189 280 (Polychromatic418967fa.accept_29_23_15_19_1_17214 81 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 280 (accept_3_3 80 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 189 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 78 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 77 189 280 7 11 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 76 189 280 (Polychromatic418967fa.accept_15_1_9_10_1_2327 76 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 280
  (Polychromatic418967fa.accept_16_11_13_8_1_1578 75 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 189 280 (accept_3_3 74 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 189 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 189
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 280 (accept_3_3 71 189
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 189 280 7 10 27 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 189 280
  (Polychromatic418967fa.accept_16_5_13_8_1_2454 69 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 189 280 (accept_3_3 68 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 189 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 66 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 280 (accept_3_3 65 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 64 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 189 280 7 9 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 189 280 (accept_3_3 62
  189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 61 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 189 280 (Polychromatic418967fa.accept_16_12_13_8_1_2409 60 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 280 (accept_3_3 59 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 280 (Polychromatic418967fa.accept_19_1_18_14_1_6392 58 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 189 280 7 8 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 280
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 189 280 (accept_3_3 53 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 189 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 189 280 (Polychromatic418967fa.accept_16_3_13_8_1_1594 51 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 280 (accept_3_3 50 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 49 189 280 7 7 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 189 280 (Polychromatic418967fa.accept_15_3_9_10_1_2325
  48 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 280 (accept_3_3 47
  189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 46 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 189 280 (Polychromatic418967fa.accept_17_11_2_8_1_7569 45 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 280 (accept_3_3 44 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 189 280 7 6 27 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 189 280 (accept_3_3 41 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 280 (Polychromatic418967fa.accept_22_18_13_16_1_9562 40
  189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 280
  (Polychromatic418967fa.accept_19_1_18_14_1_6392 39 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 280 (accept_3_3 38 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 280 (Polychromatic418967fa.accept_16_4_13_8_1_3424 36 189
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 189 280 7 5 27 40 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 189 280
  (Polychromatic418967fa.accept_15_4_9_10_1_5384 34 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 189 280 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 280 (accept_3_3 32 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 280 (Polychromatic418967fa.accept_11_8_2_5_1_1769
  30 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 280 (accept_3_3 29
  189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 189 280 7 4 27 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 189 280
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 280 (accept_3_3 26 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 280 (Polychromatic418967fa.accept_22_2_13_16_1_6117 24 189
  280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 280 (accept_3_3 23 189
  280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 280
  (Polychromatic418967fa.accept_19_3_18_14_1_5020 22 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 189 280 7 3 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 189 280 (accept_3_3 20 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 280 (accept_3_3 17 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 280
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 189 280 (Polychromatic418967fa.accept_18_15_9_10_1_1082 15 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 189 280 7 2 27 40 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 189 280
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 189 280 (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 280 (accept_3_3 11 189 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 280 (Polychromatic418967fa.accept_17_10_2_8_1_6295 10 189 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 280
  (Polychromatic418967fa.accept_22_9_13_16_1_17213 9 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 280 (accept_3_3 8 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 189 280 7 1 27 40 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 189 280 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 280 (accept_3_3 5 189 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 189 280 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 189 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 280
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 280 (accept_3_3 2 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 280 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 188 280
  (Eq.refl Bool.true) (allA_of_3_1 93 188 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 187 280 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 187 280 (accept_3_3 92 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 187 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 91 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 187 280
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 90 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 187 280 (accept_3_3 89 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 187 280 (Polychromatic418967fa.accept_19_12_16_14_1_3661 88 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 187 280 (accept_3_3 86 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 85 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 187 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 84 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 187 280 (accept_3_3 83 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 187 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 82 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 187 280 (accept_3_3 80 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 187 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 79 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 187 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 187 280 (accept_3_3 77 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 187 280 (accept_3_3 74 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 187 280 (Polychromatic418967fa.accept_21_10_19_7_1_3719 73 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 187 280
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 72 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 187 280 (accept_3_3 71 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 187 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 187 280 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 187 280 (accept_3_3 68 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379
  67 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 187 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 187 280 (accept_3_3 65 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 187 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 64 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 187 280 (accept_3_3 62 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 187 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 187 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 187 280 (accept_3_3 59 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 187 280 (accept_3_3 56 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 187 280 (Polychromatic418967fa.accept_19_17_16_14_1_10604 55 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 187 280
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 187 280 (accept_3_3 53 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 187 280 (Polychromatic418967fa.accept_16_4_11_8_1_1574 52 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 187 280 (accept_3_3 50 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 187 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 187 280 (accept_3_3 47 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 187 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 187 280 (accept_3_3 44 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 187 280 (Polychromatic418967fa.accept_19_5_16_14_1_2374 43 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 187 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 187 280 (accept_3_3 41 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 187 280 (accept_3_3 38 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 187 280 (Polychromatic418967fa.accept_13_11_5_7_1_2420 37 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 187 280
  (Polychromatic418967fa.accept_16_4_11_8_1_1574 36 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 187 280 (accept_3_3 35 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 187 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 280 (accept_3_3 32 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 280 (accept_3_3 29 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 280 (Polychromatic418967fa.accept_13_2_5_7_1_1695 28 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 280 (accept_3_3 26 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 280 (Polychromatic418967fa.accept_13_12_5_7_1_1696 25 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 280 (accept_3_3 23 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 280 (accept_3_3 20 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 280 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 280
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 280 (accept_3_3 17 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 280 (accept_3_3 14 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 280
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 280 (accept_3_3 11 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 280 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 280 (accept_3_3 8 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 280 (Polychromatic418967fa.accept_22_7_11_16_1_17212 7 187 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 280
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 280 (accept_3_3 5 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 280 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 187 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 280 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 280 (accept_3_3 2 187 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 280 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 187 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 186
  280 (Eq.refl Bool.true) (allA_succ_of_gcd 94 186 280 2 47 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 93 186 280
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 186 280 2 46 93 140 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 186 280
  (Polychromatic418967fa.accept_15_1_6_10_1_23 91 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 186 280 2 45 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 280 (accept_3_3 89 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 186 280 2 44 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 186 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 186 280 2 43 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 186 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 85 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 186 280 2 42 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 186 280 (accept_3_3 83 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 186 280 2 41 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 186 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 81 186 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 186 280 2 40 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 186 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 79 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 186 280 2 39 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 186 280 (accept_3_3 77 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 186 280 2 38 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 186 280 2 37 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 186 280
  (Polychromatic418967fa.accept_21_10_18_7_1_5212 73 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 186 280 2 36 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 186 280 (accept_3_3 71 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 186 280 2 35 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 186 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 186 280 2 34 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 186 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 67 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 280 2 33 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 280 (accept_3_3 65 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 186 280 2 32 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 186 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 186 280 2 31 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 186 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 61 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 280 2 30 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 280 (accept_3_3 59 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 186 280 2 29 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 186 280 2 28 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 186 280
  (Polychromatic418967fa.accept_13_3_4_7_1_1711 55 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 280 2 27 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 280 (accept_3_3 53 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 186 280 2 26 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 186 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 186 280 2 25 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 186 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 49 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 280 2 24 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 280 (accept_3_3 47 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 186 280 2 23 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 186 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 186 280 2 22 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 186 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 43 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 280 2 21 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 280 (accept_3_3 41 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 186 280 2 20 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 186 280 2 19 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 186 280
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 280 2 18 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 280 (accept_3_3 35 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 186 280 2 17 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 186 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 280 2 16 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 31 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 280 2 15 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 280 (accept_3_3 29 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 186 280 2 14 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 186 280 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 280 2 13 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 25 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 280 2 12 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 280 (accept_3_3 23 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 280 2 11 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 280 2 10 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 280
  (Polychromatic418967fa.accept_13_6_4_7_1_2464 19 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 280 2 9 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 280 (accept_3_3 17 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 280 2 8 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 280 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 186 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 280 2 7 93 140 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 280
  (Polychromatic418967fa.accept_9_4_6_1_1_393 13 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 280 2 6 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 280 (accept_3_3 11 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 280 2 5 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 280 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 186 280 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 280 2 4 93 140 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 280
  (Polychromatic418967fa.accept_9_7_6_1_1_709 7 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 280 2 3 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 280 (accept_3_3 5 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  280 2 2 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 280 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 186 280 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 280 2 1 93 140 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 280 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 186 280 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  280)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_280_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


