-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch278
-- name    : Polychromatic418967fa_Branch278
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:32:58.811752+00:00
-- url     : https://prove2.me/theorems/0b404bb6-eba2-4453-9f2d-73707145cc1a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch278_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_278 : allB 278 278 :=
  allB_succ' 2 277 278 (Eq.refl Bool.true) (allA_of_3_0 2 277 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  276 278 (Eq.refl Bool.true) (allA_succ_of_gcd 2 276 278 2 1 138 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 278 (accept_3_2 1 276 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 276 278))) (allB_succ' 4 275 278 (Eq.refl Bool.true) (allA_succ_of_accept 3 275 278
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 275 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 275 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 275 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 275 278 (accept_3_2 1 275 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 275 278)))) (allB_succ' 5 274 278 (Eq.refl Bool.true) (allA_of_3_0 5 274 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 273 278 (Eq.refl Bool.true) (allA_succ_of_accept 5 273 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 273 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 273 278 (accept_3_2 4 273 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  273 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 273 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 273 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 273 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 278 (accept_3_2 1 273 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 273 278)))))) (allB_succ' 7 272 278 (Eq.refl Bool.true) (allA_succ_of_gcd 6 272 278 2 3
  136 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 272 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 272 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 272 278 2 2 136 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 272 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 272 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 272 278 2 1 136 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 272 278 (accept_3_2 1 272 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 272 278))))))) (allB_succ' 8 271 278 (Eq.refl Bool.true) (allA_of_3_0 8 271
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 270 278 (Eq.refl Bool.true) (allA_succ_of_gcd 8 270 278 2 4
  135 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 270 278
  (accept_3_2 7 270 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 270 278 2 3 135 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 270 278
  (Polychromatic418967fa.accept_19_5_4_12_1_7773 5 270 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 270 278 2 2 135 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 270 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 270 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 270 278 2 1 135 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 278 (accept_3_2 1 270 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 270 278))))))))) (allB_succ' 10 269 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 269 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 269 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 269 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 269 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 269 278 (accept_3_2 7 269 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 269 278 (Polychromatic418967fa.accept_15_6_14_8_1_245
  6 269 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 269 278
  (Polychromatic418967fa.accept_14_5_3_12_1_324 5 269 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 269 278 (accept_3_2 4 269 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  269 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 269 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 269 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 269 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 278 (accept_3_2 1 269 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 269 278)))))))))) (allB_succ' 11 268 278 (Eq.refl Bool.true) (allA_of_3_0 11 268 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 267 278 (Eq.refl Bool.true) (allA_succ_of_accept 11 267 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 267 278 (accept_3_2 10 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  267 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 267 278 (Polychromatic418967fa.accept_19_8_1_12_1_4804 8 267 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 278 (accept_3_2 7 267 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 267 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 267 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 267 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 267 278 (accept_3_2 4 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  267 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 267 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 267 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 267 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 278 (accept_3_2 1 267 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 267 278)))))))))))) (allB_succ' 13 266 278 (Eq.refl Bool.true) (allA_succ_of_gcd 12 266
  278 2 6 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 266 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 266 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 266 278 2 5 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 266 278 (Polychromatic418967fa.accept_21_9_14_5_1_8160 9 266 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 266 278 2 4 133 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 266 278 (accept_3_2 7 266 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 266 278 2 3 133 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 266 278
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 266 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 266 278 2 2 133 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 266 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 266 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 266 278 2 1 133 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 266 278 (accept_3_2 1 266 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 266 278))))))))))))) (allB_succ' 14 265 278 (Eq.refl Bool.true) (allA_of_3_0
  14 265 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 264 278 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  264 278 2 7 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 264 278 (accept_3_2 13 264 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  264 278 2 6 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 264 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 264 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 264 278 2 5 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 264 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 9
  264 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 264 278 2 4 132 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 264 278 (accept_3_2 7
  264 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264 278 2 3 132 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 264 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 264 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 264 278 2 2 132 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 264 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 264 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 264 278 2 1 132 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 278 (accept_3_2 1 264 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 264 278))))))))))))))) (allB_succ' 16 263 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 263 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 263 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 263 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 263 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 278 (accept_3_2 13 263 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 278 (Polychromatic418967fa.accept_9_3_2_8_1_108
  12 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 263 278
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 263 278 (accept_3_2 10 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  263 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 263 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 263 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 278 (accept_3_2 7 263 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 263 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 263 278 (accept_3_2 4 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  263 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 263 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 263 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 263 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 278 (accept_3_2 1 263 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 263 278)))))))))))))))) (allB_succ' 17 262 278 (Eq.refl Bool.true) (allA_of_3_0 17 262
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 261 278 (Eq.refl Bool.true) (allA_succ_of_accept 17 261
  278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 261 278 (accept_3_2 16 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 261 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 261 278 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 261 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 261 278 (accept_3_2 13 261 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 261 278 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 261
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 261 278 (accept_3_2 10 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  261 278 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 261 278 (Polychromatic418967fa.accept_13_8_1_5_1_3176 8 261 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 278 (accept_3_2 7 261 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 261 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 278 (accept_3_2 4 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  261 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 261 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 261 278 (Polychromatic418967fa.accept_15_2_6_8_1_754 2 261 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 278 (accept_3_2 1 261 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 261 278)))))))))))))))))) (allB_succ' 19 260 278 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 260 278 2 9 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 260 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 260 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 260 278 2 8 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 260 278 (Polychromatic418967fa.accept_11_4_7_3_1_289
  15 260 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 260 278 2 7 130 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 260 278
  (accept_3_2 13 260 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 260 278 2 6 130 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 260 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 260 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 260 278 2 5 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 260 278 (Polychromatic418967fa.accept_23_9_7_2_1_17078 9 260 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 260 278 2 4 130 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 260 278 (accept_3_2 7 260 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 260 278 2 3 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 260 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5
  260 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 260 278 2 2 130 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 260 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 260 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 260 278 2 1 130 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 260 278 (accept_3_2 1 260 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  278))))))))))))))))))) (allB_succ' 20 259 278 (Eq.refl Bool.true) (allA_of_3_0 20 259 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 258 278 (Eq.refl Bool.true) (allA_succ_of_gcd 20 258 278 2 10 129 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 258 278 (accept_3_2 19 258 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 258 278 2 9 129 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 258 278
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 258 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 258 278 2 8 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 258 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 258 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 258 278 2 7 129 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 258 278 (accept_3_2 13 258 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 258 278 2 6 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 258 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11
  258 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 258 278 2 5 129 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 258 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 258 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 258 278 2 4 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 258 278 (accept_3_2 7 258 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 278 2 3 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 258 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 258 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 258 278 2 2 129 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 258 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 258 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 258 278 2 1 129 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 258 278 (accept_3_2 1 258 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258
  278))))))))))))))))))))) (allB_succ' 22 257 278 (Eq.refl Bool.true) (allA_succ_of_accept 21 257 278
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 257 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 257 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 257 278 (accept_3_2 19 257 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 257 278 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 257 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 278
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 257 278 (accept_3_2 16 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 257 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 257 278 (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 257 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 278 (accept_3_2 13 257 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 257 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 257 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 257 278 (accept_3_2 10 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  257 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 257 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 257 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 278 (accept_3_2 7 257 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 257 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 278
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 257 278 (accept_3_2 4 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  257 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 257 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 257 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 257 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 278 (accept_3_2 1 257 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 257 278)))))))))))))))))))))) (allB_succ' 23 256 278 (Eq.refl Bool.true) (allA_of_3_0
  23 256 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 255 278 (Eq.refl Bool.true) (allA_succ_of_accept 23
  255 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 255 278 (accept_3_2 22 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 255 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 255 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 255 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 255 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 255 278 (accept_3_2 19 255 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 255 278 (Polychromatic418967fa.accept_12_6_3_2_1_743
  18 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 255 278 (accept_3_2 16 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 255 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 255 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 278 (accept_3_2 13 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 255 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 255 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 255 278 (accept_3_2 10 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  255 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 255 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 278 (accept_3_2 7 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 255 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 255 278 (accept_3_2 4 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  255 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 255 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 255 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 278 (accept_3_2 1 255 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 255 278)))))))))))))))))))))))) (allB_succ' 25 254 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 254 278 2 12 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 254 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 254 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 254 278 2 11 127 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 254 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 254 278 2 10 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 254 278 (accept_3_2 19 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 254 278 2 9 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 254 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 254 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 254 278 2 8 127 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 254 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 254 278 2 7 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 254 278 (accept_3_2 13 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 254 278 2 6 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 254 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 254 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 254 278 2 5 127 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 254 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 254 278 2 4 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 254 278 (accept_3_2 7 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 254 278 2 3 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 254 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 254 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 254 278 2 2 127 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 254 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 254 278 2 1 127 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 254 278 (accept_3_2 1 254 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  278))))))))))))))))))))))))) (allB_succ' 26 253 278 (Eq.refl Bool.true) (allA_of_3_0 26 253 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 252 278 (Eq.refl Bool.true) (allA_succ_of_gcd 26 252 278 2 13 126 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 252 278 (accept_3_2 25
  252 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 252 278 2 12 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 252 278
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 252 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 252 278 2 11 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 252 278 (Polychromatic418967fa.accept_22_21_10_14_1_11003 21 252 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 252 278 2 10 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 252 278 (accept_3_2 19 252 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 252 278 2 9 126 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 252 278
  (Polychromatic418967fa.accept_19_17_5_12_1_4753 17 252 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 252 278 2 8 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 252 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 252 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 278 2 7 126 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 278 (accept_3_2 13 252 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 252 278 2 6 126 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 252 278
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 252 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 252 278 2 5 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 252 278 (Polychromatic418967fa.accept_19_9_5_12_1_7728 9 252 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 252 278 2 4 126 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 278 (accept_3_2 7 252 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252 278 2 3 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 252 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5
  252 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 252 278 2 2 126 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 252 278
  (Polychromatic418967fa.accept_15_3_12_8_1_738 3 252 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 252 278 2 1 126 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 252 278 (accept_3_2 1 252 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252
  278))))))))))))))))))))))))))) (allB_succ' 28 251 278 (Eq.refl Bool.true) (allA_succ_of_accept 27 251 278
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 251 278 (Polychromatic418967fa.accept_19_7_4_12_1_4769 26 251 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 251 278 (accept_3_2 25 251 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 251 278 (Polychromatic418967fa.accept_17_7_13_6_1_811 24 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 251 278
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 251 278 (accept_3_2 22 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 251 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 251 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 278 (accept_3_2 19 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 251 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 251 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 251 278 (accept_3_2 16 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 251 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 251 278 (Polychromatic418967fa.accept_13_1_4_5_1_113 14 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 278 (accept_3_2 13 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 278 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 251
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 251 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 251 278 (accept_3_2 10 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  251 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 251 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 251 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 278 (accept_3_2 7 251 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 278 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 251 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 251 278 (accept_3_2 4 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  251 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 251 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 251 278 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 251 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 278 (accept_3_2 1 251 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 251 278)))))))))))))))))))))))))))) (allB_succ' 29 250 278 (Eq.refl Bool.true)
  (allA_of_3_0 29 250 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 249 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 249 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 249 278 (accept_3_2 28 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 249 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 249 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 249 278 (Polychromatic418967fa.accept_11_4_7_3_1_289
  26 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 278 (accept_3_2 25
  249 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 249 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 249 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 249 278 (accept_3_2 22 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 249 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 249 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 249 278 (Polychromatic418967fa.accept_7_6_4_5_1_314
  20 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 278 (accept_3_2 19
  249 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 278
  (Polychromatic418967fa.accept_12_6_9_2_1_311 18 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 249 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 278 (accept_3_2 16 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 249 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 249 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 249 278 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 278 (accept_3_2 13
  249 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 249 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 278 (accept_3_2 10 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 249 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 249 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 249 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8
  249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 278 (accept_3_2 7 249
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 249 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 278 (accept_3_2 4 249 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 249 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 249 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2
  249 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 278 (accept_3_2 1 249
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 278)))))))))))))))))))))))))))))) (allB_succ' 31 248 278
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 248 278 2 15 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 248 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 248 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 248 278 2 14 124 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 248 278
  (Polychromatic418967fa.accept_19_8_1_12_1_4804 27 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 248 278 2 13 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 248 278 (accept_3_2 25 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 248 278 2 12 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 248 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 248 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 248 278 2 11 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 248 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 248 278 2 10 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 248 278 (accept_3_2 19 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 248 278 2 9 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 248 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 248 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 248 278 2 8 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 248 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 248 278 2 7 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 248 278 (accept_3_2 13 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 248 278 2 6 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 248 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 248 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 248 278 2 5 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 248 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 248 278 2 4 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 248 278 (accept_3_2 7 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 248 278 2 3 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 248 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 248 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 248 278 2 2 124 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 248 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 248 278 2 1 124 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 248 278 (accept_3_2 1 248 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  278))))))))))))))))))))))))))))))) (allB_succ' 32 247 278 (Eq.refl Bool.true) (allA_of_3_0 32 247 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 246 278 (Eq.refl Bool.true) (allA_succ_of_gcd 32 246 278 2 16 123 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 246 278
  (accept_3_2 31 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 246 278 2 15 123 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 246 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 246 278 2 14 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 246 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 246 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 246 278 2 13 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 246 278 (accept_3_2 25 246 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 246 278 2 12 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 246 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23
  246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 246 278 2 11 123 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 246 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 246 278 2 10 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 246 278 (accept_3_2 19 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 278 2 9 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 246 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 246 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 278 2 8 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 246 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 246 278 2 7 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 246 278 (accept_3_2 13 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 278 2 6 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 246 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 278 2 5 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 246 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 246 278 2 4 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 246 278 (accept_3_2 7 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 278 2 3 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 246 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 278 2 2 123 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 246 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 246 278 2 1 123 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 246 278 (accept_3_2 1 246 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  278))))))))))))))))))))))))))))))))) (allB_succ' 34 245 278 (Eq.refl Bool.true) (allA_succ_of_accept 33 245 278
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 245 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 245 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 245 278 (accept_3_2 31 245 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 245 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 245 278
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 245 278 (accept_3_2 28 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 245 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 245 278 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 245 278 (accept_3_2 25 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 245 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 245 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 245 278 (accept_3_2 22 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 245 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 245 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 245 278 (accept_3_2 19 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 245
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 278
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 245 278 (accept_3_2 16 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 245 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 245 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 278 (accept_3_2 13 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 245 278 (accept_3_2 10 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  245 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 245 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 278 (accept_3_2 7 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 245 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 278 (accept_3_2 4 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 245 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 278 (accept_3_2 1 245 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 278)))))))))))))))))))))))))))))))))) (allB_succ' 35 244 278 (Eq.refl Bool.true)
  (allA_of_3_0 35 244 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 243 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 243 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 243 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 278 (accept_3_2 34 243 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 278
  (Polychromatic418967fa.accept_21_11_12_5_1_2224 32 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 243 278 (accept_3_2 31 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 243 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 243 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 243 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 278 (accept_3_2 28 243 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 278 (Polychromatic418967fa.accept_13_1_9_5_1_1598
  27 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 278 (accept_3_2 25 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 278 (accept_3_2 22 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 243 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 278
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 278 (accept_3_2 19 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 278 (accept_3_2 16 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 278 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 243 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 278
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 278 (accept_3_2 13 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 278 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 278 (accept_3_2 10 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 243 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 278
  (Polychromatic418967fa.accept_19_8_15_12_1_2240 8 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 278 (accept_3_2 7 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 278 (accept_3_2 4 243 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 278 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 243 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 278
  (Polychromatic418967fa.accept_11_2_1_3_1_683 2 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 278 (accept_3_2 1 243 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  278)))))))))))))))))))))))))))))))))))) (allB_succ' 37 242 278 (Eq.refl Bool.true) (allA_succ_of_gcd 36 242 278 2 18
  121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 242
  278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 242 278 2 17 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 242 278 (Polychromatic418967fa.accept_16_1_2_6_1_2295 33 242 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 242 278 2 16 121 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 242 278 (accept_3_2 31 242 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 242 278 2 15 121 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 242 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 242 278 2 14 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 242 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 242 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 242 278 2 13 121 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 242 278 (accept_3_2 25 242 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 242 278 2 12 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 242 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23
  242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 242 278 2 11 121 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 242 278
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 242 278 2 10 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 242 278 (accept_3_2 19 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 242 278 2 9 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 242 278 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 242 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 278 2 8 121 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 278 2 7 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 278 (accept_3_2 13 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 278 2 6 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 278 (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 242 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 278 2 5 121 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 278 2 4 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 278 (accept_3_2 7 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 278 2 3 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 242 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 278 2 2 121 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 278
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 278 2 1 121 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 278 (accept_3_2 1 242 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  278))))))))))))))))))))))))))))))))))))) (allB_succ' 38 241 278 (Eq.refl Bool.true) (allA_of_3_0 38 241 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 240 278 (Eq.refl Bool.true) (allA_succ_of_gcd 38 240 278 2 19 120 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 240 278
  (accept_3_2 37 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 240 278 2 18 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 240 278
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 35 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 240 278 2 17 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 240 278 (Polychromatic418967fa.accept_21_12_9_5_1_6547 33 240 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 240 278 2 16 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 240 278 (accept_3_2 31 240 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 240 278 2 15 120 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 240 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 240 278 2 14 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 240 278 (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 240 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 278 2 13 120 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 240 278 (accept_3_2 25 240 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 240 278 2 12 120 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 240 278 2 11 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 240 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 240 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 240 278 2 10 120 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 240 278 (accept_3_2 19 240 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 278 2 9 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17
  240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 240 278 2 8 120 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 240 278
  (Polychromatic418967fa.accept_21_15_9_5_1_6588 15 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 240 278 2 7 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 240 278 (accept_3_2 13 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 278 2 6 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 240 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 240 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 278 2 5 120 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 278
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 240 278 2 4 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 240 278 (accept_3_2 7 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 278 2 3 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 240 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 240 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 278 2 2 120 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 278 2 1 120 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 278 (accept_3_2 1 240 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  278))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 239 278 (Eq.refl Bool.true) (allA_succ_of_accept 39 239 278
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 239 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 239 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 239 278 (accept_3_2 37 239 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 239 278 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 239 278
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 239 278 (accept_3_2 34 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 239 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 239 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 239 278 (accept_3_2 31 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 239 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 239 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 239 278 (accept_3_2 28 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 239 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 239 278 (Polychromatic418967fa.accept_19_7_11_12_1_13190 26 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 239 278 (accept_3_2 25 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 239 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 239 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 239 278
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 239 278 (accept_3_2 22 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 239 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 239 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 278 (accept_3_2 19 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 239 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 239 278 (accept_3_2 16 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 239 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 239 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 278 (accept_3_2 13 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 239 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 278 (accept_3_2 10 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 278 (accept_3_2 7 239 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 239 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 278 (accept_3_2 4 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 278 (accept_3_2 1 239 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 278)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 238 278 (Eq.refl
  Bool.true) (allA_of_3_0 41 238 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 237 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 237 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 278 (accept_3_2 40 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 237 278 (Polychromatic418967fa.accept_9_2_3_8_1_318
  38 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 278 (accept_3_2 37
  237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 237 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 36 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 278 (accept_3_2 34 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 237 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 278 (Polychromatic418967fa.accept_7_4_6_5_1_141
  32 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 278 (accept_3_2 31
  237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 237 278
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 237 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 278 (accept_3_2 28 237 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 278
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 278 (accept_3_2 25 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 278 (accept_3_2 22 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 237 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 278 (accept_3_2 19 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 278 (accept_3_2 16 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 237 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 278 (accept_3_2 13 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 278 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 278 (accept_3_2 10 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 237 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 278 (accept_3_2 7 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 278 (accept_3_2 4 237 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 237 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 278 (accept_3_2 1 237 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  278)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 236 278 (Eq.refl Bool.true) (allA_succ_of_gcd 42 236 278
  2 21 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  236 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 236 278 2 20 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 236 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 236 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 236 278 2 19 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 236 278 (accept_3_2 37 236 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 236 278 2 18 118 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 236 278
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 236 278 2 17 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 236 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 236 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 236 278 2 16 118 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 236 278 (accept_3_2 31 236 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 236 278 2 15 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 236 278 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 236 278 2 14 118 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 236 278
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 236 278 2 13 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 236 278 (accept_3_2 25 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 236 278 2 12 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 236 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 236 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 236 278 2 11 118 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 236 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 236 278 2 10 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 236 278 (accept_3_2 19 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 236 278 2 9 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 236 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 236 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 278 2 8 118 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 236 278 2 7 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 236 278 (accept_3_2 13 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 236 278 2 6 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 236 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 236 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 278 2 5 118 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 278
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 236 278 2 4 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 236 278 (accept_3_2 7 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 236 278 2 3 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 236 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 236 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 278 2 2 118 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 278 2 1 118 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 278 (accept_3_2 1 236 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  278))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 235 278 (Eq.refl Bool.true) (allA_of_3_0 44 235 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 234 278 (Eq.refl Bool.true) (allA_succ_of_gcd 44 234 278 2 22
  117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 234
  278 (accept_3_2 43 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 234 278 2 21 117 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 234 278
  (Polychromatic418967fa.accept_17_7_13_6_1_811 41 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 234 278 2 20 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 234 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 234 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 234 278 2 19 117 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 234 278 (accept_3_2 37 234 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 234 278 2 18 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 234 278
  (Polychromatic418967fa.accept_19_16_6_12_1_11776 35 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 234 278 2 17 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 234 278 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 234 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 234 278 2 16 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 278 (accept_3_2 31 234 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 234 278 2 15 117 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 234 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 234 278 2 14 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 234 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 234 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 234 278 2 13 117 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 278 (accept_3_2 25 234 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 234 278 2 12 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 234 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23
  234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 234 278 2 11 117 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 234 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 234 278 2 10 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 234 278 (accept_3_2 19 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 278 2 9 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 278 (Polychromatic418967fa.accept_15_2_9_8_1_736 17 234 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 278 2 8 117 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 234 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 234 278 2 7 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 234 278 (accept_3_2 13 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 278 2 6 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 278 (Polychromatic418967fa.accept_17_11_13_6_1_2625 11 234 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 278 2 5 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 234 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 234 278 2 4 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 234 278 (accept_3_2 7 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 278 2 3 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 278 (Polychromatic418967fa.accept_14_5_10_12_1_1454 5 234 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 278 2 2 117 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 234 278 2 1 117 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 234 278 (accept_3_2 1 234 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  278))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 233 278 (Eq.refl Bool.true) (allA_succ_of_accept 45
  233 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 233 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 233 278 (accept_3_2 43 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 233 278 (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 233
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 233 278
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 233 278 (accept_3_2 40 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 233 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 233 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 233 278 (accept_3_2 37 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 233 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 233 278 (accept_3_2 34 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 233 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 233 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 278 (accept_3_2 31 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 278 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 278
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 233 278 (accept_3_2 28 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 233 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 233 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 278 (accept_3_2 25 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 233 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 233 278 (accept_3_2 22 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 233 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 233 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 278 (accept_3_2 19 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 233 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 233 278 (accept_3_2 16 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 278 (accept_3_2 13 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 233
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 233 278 (accept_3_2 10 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  233 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 233 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 278 (accept_3_2 7 233 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 278
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 278 (accept_3_2 4 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 278 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 278 (accept_3_2 1 233 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 233 278)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 232 278
  (Eq.refl Bool.true) (allA_of_3_0 47 232 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 231 278 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 231 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 278 (accept_3_2 46 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 231 278
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 44 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 231 278 (accept_3_2 43 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 231 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 278 (accept_3_2 40 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 231 278 (accept_3_2 37 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 231 278 (Polychromatic418967fa.accept_19_17_3_12_1_13140 36 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 278 (accept_3_2 34 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 231 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 278 (accept_3_2 31 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 231 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 278 (accept_3_2 28 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 278 (Polychromatic418967fa.accept_20_7_11_18_1_7117 27 231 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 278
  (Polychromatic418967fa.accept_19_7_3_12_1_4787 26 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 278 (accept_3_2 25 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 278 (Polychromatic418967fa.accept_22_2_11_14_1_7783 24 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 278 (accept_3_2 22 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 278 (accept_3_2 19 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 278 (accept_3_2 16 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 278 (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 231 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 278 (accept_3_2 13 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 278 (accept_3_2 10 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 278
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 278 (accept_3_2 7 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 278 (accept_3_2 4 231 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 231 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 278 (accept_3_2 1 231 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  278)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 230 278 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  230 278 2 24 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 230 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 230 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 230 278 2 23 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 230 278
  (Polychromatic418967fa.accept_20_5_10_18_1_5622 45 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 230 278 2 22 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 230 278 (accept_3_2 43 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 230 278 2 21 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 230 278 (Polychromatic418967fa.accept_13_2_9_5_1_959 41 230 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 230 278 2 20 115 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 230 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 230 278 2 19 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 230 278 (accept_3_2 37 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 230 278 2 18 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 230 278 (Polychromatic418967fa.accept_20_15_10_18_1_8658 35 230 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 230 278 2 17 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 230 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 230 278 2 16 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 230 278 (accept_3_2 31 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 230 278 2 15 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 230 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 230 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 230 278 2 14 115 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 230 278
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 230 278 2 13 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 230 278 (accept_3_2 25 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 230 278 2 12 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 230 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 230 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 230 278 2 11 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 230 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 230 278 2 10 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 230 278 (accept_3_2 19 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 230 278 2 9 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 230 278 (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 230 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 278 2 8 115 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 278 2 7 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 278 (accept_3_2 13 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 278 2 6 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 230 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 278 2 5 115 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 278
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 9 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 278 2 4 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 278 (accept_3_2 7 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 278 2 3 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 5 230 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 278 2 2 115 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 278 2 1 115 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 278 (accept_3_2 1 230 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  278))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 229 278 (Eq.refl Bool.true) (allA_of_3_0 50 229
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 228 278 (Eq.refl Bool.true) (allA_succ_of_gcd 50 228 278 2
  25 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 228
  278 (accept_3_2 49 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 228 278 2 24 114 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 228 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 228 278 2 23 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 228 278 (Polychromatic418967fa.accept_16_13_4_6_1_2322 45 228 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 228 278 2 22 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 228 278 (accept_3_2 43 228 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 228 278 2 21 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 228 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 228 278 2 20 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 228 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 228 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 228 278 2 19 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 278 (accept_3_2 37 228 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 228 278 2 18 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 228 278
  (Polychromatic418967fa.accept_15_5_3_8_1_748 35 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 228 278 2 17 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 228 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 228 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 278 2 16 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 278 (accept_3_2 31 228 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 278 2 15 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 278 2 14 114 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 228 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 228 278 2 13 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 228 278 (accept_3_2 25 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 278 2 12 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 228 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 228 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 278 2 11 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 278
  (Polychromatic418967fa.accept_16_5_4_6_1_3349 21 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 228 278 2 10 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 228 278 (accept_3_2 19 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 278 2 9 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 228 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 228 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 278 2 8 114 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 228 278 2 7 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 228 278 (accept_3_2 13 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 228 278 2 6 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 228 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 228 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 278 2 5 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 278 2 4 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 228 278 (accept_3_2 7 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 278 2 3 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 228 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 228 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 278 2 2 114 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 278
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 278 2 1 114 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 278 (accept_3_2 1 228 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  278))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 227 278 (Eq.refl Bool.true) (allA_succ_of_accept
  51 227 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 227 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 227 278 (accept_3_2 49 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 227 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 227 278
  (Polychromatic418967fa.accept_14_5_3_12_1_324 47 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 227 278 (accept_3_2 46 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 227 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 227 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 227 278 (accept_3_2 43 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 227 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 227 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 227 278 (accept_3_2 40 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 227 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 227 278 (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 278 (accept_3_2 37 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 227 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 227 278
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 227 278 (accept_3_2 34 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 227 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 227 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 278 (accept_3_2 31 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 227 278 (accept_3_2 28 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 227 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 26 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 278 (accept_3_2 25 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 227 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 278 (accept_3_2 22 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 278 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 278 (accept_3_2 19 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 278 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 227
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 278 (accept_3_2 16 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 278 (accept_3_2 13 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 278
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 278 (accept_3_2 10 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 278 (accept_3_2 7 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 227 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 278 (accept_3_2 4 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 278 (accept_3_2 1 227 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 278)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 226 278
  (Eq.refl Bool.true) (allA_of_3_0 53 226 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 225 278 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 225 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 225 278 (accept_3_2 52 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 225 278
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 50 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 225 278 (accept_3_2 49 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 225 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 278 (accept_3_2 46 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 225 278
  (Polychromatic418967fa.accept_17_10_4_6_1_3757 44 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 225 278 (accept_3_2 43 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 225 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 225 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 278 (accept_3_2 40 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 225 278 (accept_3_2 37 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 225 278 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 278 (accept_3_2 34 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 278 (accept_3_2 31 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 225 278 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 225 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 278 (accept_3_2 28 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 278
  (Polychromatic418967fa.accept_19_7_16_12_1_10556 26 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 225 278 (accept_3_2 25 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 225 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 225 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 225 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 278 (accept_3_2 22 225 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 278 (Polychromatic418967fa.accept_16_5_1_6_1_3367
  21 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 278 (accept_3_2 19 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 278 (accept_3_2 16 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 278
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 278 (accept_3_2 13 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 278 (accept_3_2 10 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 278 (accept_3_2 7 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 278 (accept_3_2 4 225 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 225 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 278 (accept_3_2 1 225 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 224 278 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 224 278 2 27 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 224 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 224 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 224 278 2 26 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 224 278 (Polychromatic418967fa.accept_11_7_4_3_1_302
  51 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 224 278 2 25 112 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 224 278
  (accept_3_2 49 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 224 278 2 24 112 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 224 278
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 224 278 2 23 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 224 278 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 224 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 224 278 2 22 112 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 224 278 (accept_3_2 43 224 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 224 278 2 21 112 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 224 278
  (Polychromatic418967fa.accept_12_5_8_2_1_309 41 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 224 278 2 20 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 224 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 224 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 224 278 2 19 112 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 224 278 (accept_3_2 37 224 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 224 278 2 18 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 224 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274
  35 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 224 278 2 17 112 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 224 278
  (Polychromatic418967fa.accept_21_12_14_5_1_8204 33 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 224 278 2 16 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 224 278 (accept_3_2 31 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 224 278 2 15 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 224 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 224 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 224 278 2 14 112 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 278
  (Polychromatic418967fa.accept_13_1_3_5_1_140 27 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 224 278 2 13 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 224 278 (accept_3_2 25 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 224 278 2 12 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 224 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 224 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 278 2 11 112 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 278
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 278 2 10 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 224 278 (accept_3_2 19 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 224 278 2 9 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 224 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 224 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 278 2 8 112 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 278
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 278 2 7 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 278 (accept_3_2 13 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 278 2 6 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 224 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 224 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 278 2 5 112 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 278 2 4 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 278 (accept_3_2 7 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 278 2 3 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 224 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 278 2 2 112 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 278
  (Polychromatic418967fa.accept_19_3_15_12_1_9110 3 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 278 2 1 112 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 278 (accept_3_2 1 224 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 223 278 (Eq.refl Bool.true) (allA_of_3_0 56
  223 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 222 278 (Eq.refl Bool.true) (allA_succ_of_gcd 56 222
  278 2 28 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  55 222 278 (accept_3_2 55 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 222 278 2 27 111 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 222 278
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 53 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 222 278 2 26 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 222 278 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 222 278 2 25 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 222 278 (accept_3_2 49 222 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 222 278 2 24 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 222 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47
  222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 222 278 2 23 111 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 222 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 222 278 2 22 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 222 278 (accept_3_2 43 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 222 278 2 21 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 222 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 222 278 2 20 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 222 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 222 278 2 19 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 222 278 (accept_3_2 37 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 278 2 18 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 278 2 17 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 222 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 222 278 2 16 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 222 278 (accept_3_2 31 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 278 2 15 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 278 2 14 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 222 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 222 278 2 13 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 222 278 (accept_3_2 25 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 278 2 12 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 278 2 11 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 278 2 10 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 278 (accept_3_2 19 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 278 2 9 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 278 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 222 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 278 2 8 111 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 278 2 7 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 278 (accept_3_2 13 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 278 2 6 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 278 2 5 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 278 2 4 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 278 (accept_3_2 7 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 278 2 3 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 222 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 278 2 2 111 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 278 2 1 111 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 278 (accept_3_2 1 222 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 221 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 221 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 221 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 221 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 221 278 (accept_3_2 55 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 221 278
  (Polychromatic418967fa.accept_21_12_11_5_1_6549 54 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 221 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 221 278 (accept_3_2 52 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 221 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 221 278 (accept_3_2 49 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 221 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 221 278 (accept_3_2 46 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 221 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 221 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 221 278 (accept_3_2 43 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 221 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 221 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 221 278 (accept_3_2 40 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 221 278 (accept_3_2 37 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 221 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 278 (accept_3_2 34 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 221 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 221 278 (accept_3_2 31 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 221 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 278 (accept_3_2 28 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 278
  (Polychromatic418967fa.accept_23_3_14_2_1_15600 26 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 221 278 (accept_3_2 25 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 221 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 221 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 278 (accept_3_2 22 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 278 (accept_3_2 19 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 278 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 278 (Polychromatic418967fa.accept_18_17_5_8_1_1898 17 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 278 (accept_3_2 16 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 278
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 278 (accept_3_2 13 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 278 (accept_3_2 10 221 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 278 (accept_3_2 7 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 278 (Polychromatic418967fa.accept_15_5_11_8_1_1391 5 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 278 (accept_3_2 4 221 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 278 (accept_3_2 1 221 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 220 278 (Eq.refl Bool.true) (allA_of_3_0
  59 220 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 219 278 (Eq.refl Bool.true) (allA_succ_of_accept 59
  219 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 219 278 (accept_3_2 58 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 219 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 219 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 219 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 219 278 (accept_3_2 55 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 219 278 (Polychromatic418967fa.accept_10_4_9_8_1_125
  54 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 219 278 (accept_3_2 52 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 219 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 219 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 278 (accept_3_2 49 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 219 278 (accept_3_2 46 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 219 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 219 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 278 (accept_3_2 43 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 219 278 (accept_3_2 40 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 219 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 278 (accept_3_2 37 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 278 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 278 (accept_3_2 34 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 219 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 219 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 278 (accept_3_2 31 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 278 (accept_3_2 28 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 278 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 278 (Polychromatic418967fa.accept_17_9_15_6_1_3744 26 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 278 (accept_3_2 25 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 278 (accept_3_2 22 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 278 (accept_3_2 19 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 278 (accept_3_2 16 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 278 (accept_3_2 13 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 278 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 278 (accept_3_2 10 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 278 (Polychromatic418967fa.accept_17_8_15_6_1_4889 8 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 278 (accept_3_2 7 219 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 219 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 278 (accept_3_2 4 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 219 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 278 (accept_3_2 1 219 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 218
  278 (Eq.refl Bool.true) (allA_succ_of_gcd 60 218 278 2 30 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 218 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 218 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 218 278 2 29 109 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 218 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 218 278 2 28 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 218 278 (accept_3_2 55 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 218 278 2 27 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 218 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 218 278 2 26 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 218 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 51 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 218 278 2 25 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 218 278 (accept_3_2 49 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 218 278 2 24 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 218 278 (Polychromatic418967fa.accept_13_8_10_5_1_977 47 218 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 218 278 2 23 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 218 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 218 278 2 22 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 218 278 (accept_3_2 43 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 218 278 2 21 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 218 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 218 278 2 20 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 278 2 19 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 278 (accept_3_2 37 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 278 2 18 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 278 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 218 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 278 2 17 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 218 278 2 16 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 218 278 (accept_3_2 31 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 278 2 15 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 278 (Polychromatic418967fa.accept_19_10_9_12_1_4774 29 218 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 278 2 14 109 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 278 2 13 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 278 (accept_3_2 25 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 278 2 12 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 278 2 11 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 278 2 10 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 278 (accept_3_2 19 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 278 2 9 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 278 2 8 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 278 2 7 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 278 (accept_3_2 13 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 278 2 6 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 278 2 5 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 278
  (Polychromatic418967fa.accept_22_9_20_14_1_9412 9 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 278 2 4 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 278 (accept_3_2 7 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 278 2 3 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 218 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 278 2 2 109 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 278 2 1 109 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 278 (accept_3_2 1 218 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 217 278 (Eq.refl Bool.true)
  (allA_of_3_0 62 217 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 216 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 216 278 2 31 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 216 278 (accept_3_2 61 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 216 278 2 30 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 216 278 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 216 278 2 29 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 216 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 216 278 2 28 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 216 278 (accept_3_2 55 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 216 278 2 27 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 216 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 216 278 2 26 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 216 278
  (Polychromatic418967fa.accept_13_12_8_5_1_976 51 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 216 278 2 25 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 216 278 (accept_3_2 49 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 216 278 2 24 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 216 278 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 216 278 2 23 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 216 278
  (Polychromatic418967fa.accept_17_11_12_6_1_6070 45 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 216 278 2 22 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 216 278 (accept_3_2 43 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 216 278 2 21 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 216 278 (Polychromatic418967fa.accept_14_13_6_12_1_3126 41 216 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 216 278 2 20 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 216 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 216 278 2 19 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 216 278 (accept_3_2 37 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 278 2 18 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 216 278 (Polychromatic418967fa.accept_17_1_12_6_1_3735 35 216 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 278 2 17 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 278 2 16 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 216 278 (accept_3_2 31 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 278 2 15 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 216 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 278 2 14 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 278
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 216 278 2 13 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 216 278 (accept_3_2 25 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 278 2 12 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 216 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 216 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 278 2 11 108 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 216 278
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 216 278 2 10 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 216 278 (accept_3_2 19 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 216 278 2 9 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 216 278 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 278 2 8 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 216 278 2 7 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 216 278 (accept_3_2 13 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 278 2 6 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 216 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 278 2 5 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 216 278
  (Polychromatic418967fa.accept_25_9_16_3_1_15452 9 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 216 278 2 4 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 216 278 (accept_3_2 7 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 278 2 3 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 216 278 (Polychromatic418967fa.accept_19_5_7_12_1_2252 5 216 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 278 2 2 108 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 278 2 1 108 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 278 (accept_3_2 1 216 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 215 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 215 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 215 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 215
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 215 278 (accept_3_2 61 215
  278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 215 278
  (Polychromatic418967fa.accept_29_2_12_17_1_17077 60 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 215 278 (Polychromatic418967fa.accept_14_3_5_12_1_4000 59 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 215 278 (accept_3_2 58 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 215 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 215 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 215 278 (accept_3_2 55 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 215 278 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 215 278 (accept_3_2 52 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 215 278
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 215 278 (accept_3_2 49 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 215 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 215 278 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 278 (accept_3_2 46 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 215 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 215 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 215 278 (accept_3_2 43 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 215 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 215 278 (accept_3_2 40 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 278
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 215 278 (accept_3_2 37 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 215 278 (Polychromatic418967fa.accept_19_17_6_12_1_7757 36 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 215 278 (Polychromatic418967fa.accept_14_7_5_12_1_1439 35 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 278 (accept_3_2 34 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 215 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 215 278 (accept_3_2 31 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 215 278 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 278 (accept_3_2 28 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 278
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 215 278 (accept_3_2 25 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 215 278 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 215 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 278 (accept_3_2 22 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 215 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 278
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 215 278 (accept_3_2 19 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 215 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 278 (accept_3_2 16 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 278
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 278 (accept_3_2 13 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 278 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 278 (accept_3_2 10 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 278
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 278 (accept_3_2 7 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 278 (Polychromatic418967fa.accept_23_6_8_2_1_17076 6 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 278 (accept_3_2 4 215 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 278 (accept_3_2 1 215 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 214 278 (Eq.refl Bool.true)
  (allA_of_3_0 65 214 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 213 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 213 278 (accept_3_2 64 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 213 278 (Polychromatic418967fa.accept_11_7_4_3_1_302
  62 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 278 (accept_3_2 61
  213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 278
  (Polychromatic418967fa.accept_21_18_3_5_1_9796 60 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 213 278 (accept_3_2 58 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 213 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 278 (Polychromatic418967fa.accept_9_2_6_8_1_321
  56 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 278 (accept_3_2 55
  213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 278
  (Polychromatic418967fa.accept_12_6_9_2_1_311 54 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 213 278 (accept_3_2 52 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 50
  213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 278 (accept_3_2 49
  213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 48 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 278 (accept_3_2 46 213 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 213 278 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 213 278 (accept_3_2 43 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 213 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 278 (accept_3_2 40 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 278 (accept_3_2 37 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 213 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 278 (accept_3_2 34 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 278 (Polychromatic418967fa.accept_14_5_3_12_1_324 33 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 278 (accept_3_2 31 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 213 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 278 (accept_3_2 28 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 278 (accept_3_2 25 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 213 278 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 278 (accept_3_2 22 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 278 (accept_3_2 19 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 278 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 278 (accept_3_2 16 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 278 (accept_3_2 13 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 278 (accept_3_2 10 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 278 (accept_3_2 7 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 278 (accept_3_2 4 213 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 278 (accept_3_2 1 213 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 212 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 212 278 2 33 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 212 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 212 278 2 32 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 212 278
  (Polychromatic418967fa.accept_14_7_2_12_1_1430 63 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 212 278 2 31 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 212 278 (accept_3_2 61 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 212 278 2 30 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 212 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 212 278 2 29 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 212 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 212 278 2 28 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 212 278 (accept_3_2 55 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 212 278 2 27 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 212 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 212 278 2 26 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 212 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 212 278 2 25 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 212 278 (accept_3_2 49 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 212 278 2 24 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 212 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 278 2 23 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 278 2 22 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 278 (accept_3_2 43 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 278 2 21 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 278 2 20 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 278 2 19 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 278 (accept_3_2 37 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 278 2 18 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 212 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 278 2 17 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 212 278 2 16 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 212 278 (accept_3_2 31 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 212 278 2 15 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 212 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 278 2 14 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 278
  (Polychromatic418967fa.accept_13_1_4_5_1_113 27 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 212 278 2 13 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 212 278 (accept_3_2 25 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 278 2 12 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 212 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 212 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 278 2 11 106 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 278 2 10 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 212 278 (accept_3_2 19 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 278 2 9 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 278 2 8 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 278 2 7 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 278 (accept_3_2 13 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 278 2 6 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 278 2 5 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 278
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 278 2 4 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 278 (accept_3_2 7 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 278 2 3 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 212 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 278 2 2 106 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 278 2 1 106 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 278 (accept_3_2 1 212 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 211 278 (Eq.refl Bool.true)
  (allA_of_3_0 68 211 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 210 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 210 278 2 34 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 210 278 (accept_3_2 67 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 210 278 2 33 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 210 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 210 278 2 32 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 210 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 210 278 2 31 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 210 278 (accept_3_2 61 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 210 278 2 30 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 210 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 210 278 2 29 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 210 278
  (Polychromatic418967fa.accept_11_2_1_3_1_683 57 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 210 278 2 28 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 210 278 (accept_3_2 55 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 278 2 27 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 278 (Polychromatic418967fa.accept_26_1_2_18_1_17075 53 210 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 210 278 2 26 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 210 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 51 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 210 278 2 25 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 210 278 (accept_3_2 49 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 278 2 24 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 278 2 23 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 210 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 210 278 2 22 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 210 278 (accept_3_2 43 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 278 2 21 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 210 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 278 2 20 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 210 278 2 19 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 210 278 (accept_3_2 37 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 278 2 18 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 278 2 17 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 278 2 16 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 278 (accept_3_2 31 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 278 2 15 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 278 2 14 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 210 278 2 13 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 210 278 (accept_3_2 25 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 278 2 12 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 278 2 11 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 278 2 10 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 278 (accept_3_2 19 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 278 2 9 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 278 (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 210 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 278 2 8 105 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 278 2 7 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 278 (accept_3_2 13 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 278 2 6 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 278 2 5 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 278 2 4 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 278 (accept_3_2 7 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 278 2 3 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 210 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 278 2 2 105 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 278 2 1 105 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 278 (accept_3_2 1 210 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 209 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 209 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 209 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 209 278 (accept_3_2 67 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 209 278 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 209 278
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 209 278 (accept_3_2 64 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 209 278 (Polychromatic418967fa.accept_14_6_13_12_1_810 62 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 278 (accept_3_2 61 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 209 278 (accept_3_2 58 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 209 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 278 (accept_3_2 55 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 209
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 53 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 209 278 (accept_3_2 52 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 209 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 50 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 278 (accept_3_2 49 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 278 (accept_3_2 46 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 278 (accept_3_2 43 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 278 (accept_3_2 40 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 278 (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 278 (accept_3_2 37 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 278 (accept_3_2 34 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 278 (accept_3_2 31 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 278 (accept_3_2 28 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 278 (Polychromatic418967fa.accept_25_1_9_3_1_8289 26 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 278 (accept_3_2 25 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 278 (accept_3_2 22 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 278 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 278 (accept_3_2 19 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 209 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 278
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 278 (accept_3_2 16 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 278 (accept_3_2 13 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 278 (accept_3_2 10 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 278 (accept_3_2 7 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 209 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 278 (accept_3_2 4 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 278 (Polychromatic418967fa.accept_16_2_1_6_1_2342 2 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 278 (accept_3_2 1 209 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 208 278 (Eq.refl Bool.true) (allA_of_3_0 71 208 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 207 278 (Eq.refl Bool.true) (allA_succ_of_accept 71 207 278 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 207 278 (accept_3_2 70
  207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 207 278 (Polychromatic418967fa.accept_27_14_18_8_1_17062 68 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 278 (accept_3_2 67 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 207 278 (accept_3_2 64 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 207 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 62 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 278 (accept_3_2 61 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 278 (Polychromatic418967fa.accept_13_8_12_5_1_1604 60 207 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 207 278 (accept_3_2 58 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 207 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 207 278 (Polychromatic418967fa.accept_13_4_12_5_1_476 56 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 278 (accept_3_2 55 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 207
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 207 278 (accept_3_2 52 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 207 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 207 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 50 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 278 (accept_3_2 49 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 278 (accept_3_2 46 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 207 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 207 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 278 (accept_3_2 43 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 278 (accept_3_2 40 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 278 (Polychromatic418967fa.accept_27_11_18_8_1_15152 38 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 278 (accept_3_2 37 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 207 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 278 (accept_3_2 34 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 278 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 278 (accept_3_2 31 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 207 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 278 (accept_3_2 28 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 278 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 278 (accept_3_2 25 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 278 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 207
  278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 278 (accept_3_2 22 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 278 (accept_3_2 19 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 278 (accept_3_2 16 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 278 (accept_3_2 13 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 278 (Polychromatic418967fa.accept_21_12_18_5_1_14149 12
  207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 278 (accept_3_2 10 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 278 (accept_3_2 7 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 207 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 278
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 278 (accept_3_2 4 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 207 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 278 (accept_3_2 1 207 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 206 278 (Eq.refl Bool.true) (allA_succ_of_gcd 72 206 278 2 36 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 206 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 71 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 206 278 2 35 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 206 278 (Polychromatic418967fa.accept_17_1_2_6_1_818 69 206 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 206 278 2 34 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 206 278 (accept_3_2 67 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 206 278 2 33 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 206 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65
  206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 206 278 2 32 103 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 206 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 206 278 2 31 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 206 278 (accept_3_2 61 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 206 278 2 30 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 206 278 (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 206 278 2 29 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 206 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 206 278 2 28 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 206 278 (accept_3_2 55 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 206 278 2 27 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 206 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 206 278 2 26 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 206 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 206 278 2 25 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 206 278 (accept_3_2 49 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 206 278 2 24 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 206 278 (Polychromatic418967fa.accept_14_5_10_12_1_1454 47 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 278 2 23 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 278
  (Polychromatic418967fa.accept_13_6_11_5_1_133 45 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 278 2 22 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 278 (accept_3_2 43 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 278 2 21 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 278 (Polychromatic418967fa.accept_27_14_17_8_1_17074 41 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 278 2 20 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 278
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 278 2 19 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 278 (accept_3_2 37 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 278 2 18 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 278 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 278 2 17 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 278 2 16 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 278 (accept_3_2 31 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 278 2 15 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 206 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 278 2 14 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 278
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 278 2 13 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 278 (accept_3_2 25 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 278 2 12 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 206 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 278 2 11 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 278
  (Polychromatic418967fa.accept_17_4_2_6_1_2629 21 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 278 2 10 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 278 (accept_3_2 19 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 278 2 9 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 278 2 8 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 278 2 7 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 278 (accept_3_2 13 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 278 2 6 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 278 (Polychromatic418967fa.accept_21_11_17_5_1_8161 11 206 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 278 2 5 103 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 278 2 4 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 278 (accept_3_2 7 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 278 2 3 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 278 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 206 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 278 2 2 103 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 278 2 1 103 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 278 (accept_3_2 1 206 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 205 278 (Eq.refl
  Bool.true) (allA_of_3_0 74 205 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 204 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 204 278 2 37 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 204 278 (accept_3_2 73 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 204 278 2 36 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 204 278 (Polychromatic418967fa.accept_21_8_15_5_1_8178 71 204 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 204 278 2 35 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 204 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 69 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 204 278 2 34 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 204 278 (accept_3_2 67 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 204 278 2 33 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 204 278 2 32 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 204 278
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 204 278 2 31 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 204 278 (accept_3_2 61 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 278 2 30 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 204 278 2 29 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 204 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 204 278 2 28 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 204 278 (accept_3_2 55 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 278 2 27 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 278 2 26 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 204 278
  (Polychromatic418967fa.accept_19_13_14_12_1_4797 51 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 204 278 2 25 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 204 278 (accept_3_2 49 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 278 2 24 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 278 2 23 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 204 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 204 278 2 22 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 204 278 (accept_3_2 43 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 278 2 21 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 278 2 20 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 204 278 2 19 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 204 278 (accept_3_2 37 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 278 2 18 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 204 278 (Polychromatic418967fa.accept_19_16_14_12_1_6261 35 204 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 278 2 17 102 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 278
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 33 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 204 278 2 16 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 204 278 (accept_3_2 31 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 278 2 15 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 204 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 278 2 14 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 27 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 204 278 2 13 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 278 (accept_3_2 25 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 278 2 12 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 204 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 278 2 11 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 278 2 10 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 204 278 (accept_3_2 19 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 278 2 9 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 204 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 278 2 8 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 278
  (Polychromatic418967fa.accept_13_2_9_5_1_959 15 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 204 278 2 7 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 278 (accept_3_2 13 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 278 2 6 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 204 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 278 2 5 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 204 278 2 4 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 204 278 (accept_3_2 7 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 278 2 3 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 204 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 278 2 2 102 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 278 2 1 102 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 278 (accept_3_2 1 204 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 203 278 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 203 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 203 278 (accept_3_2 73
  203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 203 278
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 203 278 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 203 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 203 278 (accept_3_2 70 203 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 203 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 203 278 (accept_3_2 67 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 203 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 278 (accept_3_2 64 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 203 278
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 62 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 203 278 (accept_3_2 61 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 203 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 203 278 (Polychromatic418967fa.accept_21_17_14_5_1_9767 59 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 278 (accept_3_2 58 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 203 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 203 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 203 278 (accept_3_2 55 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 278 (Polychromatic418967fa.accept_19_16_13_12_1_7749 54 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 278 (accept_3_2 52 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 203 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 278
  (Polychromatic418967fa.accept_16_2_11_6_1_737 50 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 203 278 (accept_3_2 49 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 203 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 278 (accept_3_2 46 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 278 (accept_3_2 43 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 278 (accept_3_2 40 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 278 (accept_3_2 37 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 278 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 278 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 278 (accept_3_2 34 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 203 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 278 (accept_3_2 31 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 278 (accept_3_2 28 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 278
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 278 (accept_3_2 25 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 278 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 278 (accept_3_2 22 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 278 (accept_3_2 19 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 278 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 278 (accept_3_2 16 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 278
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 278 (accept_3_2 13 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 278 (accept_3_2 10 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 278 (accept_3_2 7 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 278 (accept_3_2 4 203 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 278 (accept_3_2 1 203 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 202 278 (Eq.refl
  Bool.true) (allA_of_3_0 77 202 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 201 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 201 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 201 278 (accept_3_2 76 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 201 278 (Polychromatic418967fa.accept_9_2_3_8_1_318
  74 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 201 278 (accept_3_2 73
  201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 201 278
  (Polychromatic418967fa.accept_21_9_12_5_1_317 72 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 278 (accept_3_2 70 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 278 (Polychromatic418967fa.accept_9_5_3_8_1_316
  68 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 278 (accept_3_2 67
  201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 278
  (Polychromatic418967fa.accept_12_6_9_2_1_311 66 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 201 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 278 (accept_3_2 64 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 278
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 62 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 201 278 (accept_3_2 61 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 278 (accept_3_2 58 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 278 (Polychromatic418967fa.accept_20_17_1_18_1_11536 57 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 201 278 (accept_3_2 55 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 201 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 201 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 278 (accept_3_2 52 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 278 (accept_3_2 49 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 278 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 278 (accept_3_2 46 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 278 (Polychromatic418967fa.accept_14_3_5_12_1_4000 45 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 278
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 278 (accept_3_2 43 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 278 (accept_3_2 40 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 278
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 278 (accept_3_2 37 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 278 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 278 (accept_3_2 34 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 278
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 278 (accept_3_2 31 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 278 (accept_3_2 28 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 278
  (Polychromatic418967fa.accept_19_7_11_12_1_13190 26 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 201 278 (accept_3_2 25 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 278 (accept_3_2 22 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 278
  (Polychromatic418967fa.accept_14_7_5_12_1_1439 21 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 278 (accept_3_2 19 201 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 278 (accept_3_2 16 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 278 (accept_3_2 13 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 278 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 278
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 278 (accept_3_2 10 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 278 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 278 (Polychromatic418967fa.accept_17_8_14_6_1_8727 8 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 278 (accept_3_2 7 201 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 278 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 201 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 278
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 278 (accept_3_2 4 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 278 (accept_3_2 1 201 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 200 278 (Eq.refl Bool.true) (allA_succ_of_gcd 78 200 278 2 39 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 200 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 200 278 2 38 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 200 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 75 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 200 278 2 37 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 200 278 (accept_3_2 73 200 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 200 278 2 36 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 200 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 71
  200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 200 278 2 35 100 139
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 200 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 200 278 2 34 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 200 278 (accept_3_2 67 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 200 278 2 33 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 200 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 200 278 2 32 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 200 278
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 200 278 2 31 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 200 278 (accept_3_2 61 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 200 278 2 30 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 200 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 200 278 2 29 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 200 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 200 278 2 28 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 200 278 (accept_3_2 55 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 200 278 2 27 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 200 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 278 2 26 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 200 278 2 25 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 200 278 (accept_3_2 49 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 200 278 2 24 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 200 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 200 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 200 278 2 23 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 200 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 200 278 2 22 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 200 278 (accept_3_2 43 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 200 278 2 21 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 200 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 278 2 20 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 200 278 2 19 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 278 (accept_3_2 37 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 200 278 2 18 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 200 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 200 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 200 278 2 17 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 278
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 200 278 2 16 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 200 278 (accept_3_2 31 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 200 278 2 15 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 200 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 278 2 14 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 278 2 13 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 200 278 (accept_3_2 25 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 278 2 12 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 200 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 278 2 11 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 278 2 10 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 278 (accept_3_2 19 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 278 2 9 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 278 2 8 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 278 2 7 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 278 (accept_3_2 13 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 278 2 6 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 200 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 278 2 5 100 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 278 2 4 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 278 (accept_3_2 7 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 278 2 3 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 278 2 2 100 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 278
  (Polychromatic418967fa.accept_9_3_2_8_1_108 3 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 278 2 1 100 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 278 (accept_3_2 1 200 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 199 278 (Eq.refl
  Bool.true) (allA_of_3_0 80 199 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 198 278 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 198 278 2 40 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 198 278 (accept_3_2 79 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 198 278 2 39 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 198 278 (Polychromatic418967fa.accept_14_7_2_12_1_1430 77 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 198 278 2 38 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 198 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 198 278 2 37 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 198 278 (accept_3_2 73 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 198 278 2 36 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 198 278 (Polychromatic418967fa.accept_13_6_3_5_1_3167 71 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 278 2 35 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 198 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 198 278 2 34 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 198 278 (accept_3_2 67 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 278 2 33 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 198 278 (Polychromatic418967fa.accept_15_5_3_8_1_748 65 198 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 278 2 32 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 198 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 198 278 2 31 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 198 278 (accept_3_2 61 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 278 2 30 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 198 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 278 2 29 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 198 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 198 278 2 28 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 198 278 (accept_3_2 55 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 278 2 27 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 198 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 278 2 26 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 278 2 25 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 278 (accept_3_2 49 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 278 2 24 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 198 278 (Polychromatic418967fa.accept_13_8_3_5_1_1636 47 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 278 2 23 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 45 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 278 2 22 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 278 (accept_3_2 43 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 278 2 21 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 278 2 20 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 39 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 278 2 19 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 278 (accept_3_2 37 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 278 2 18 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 278 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 278 2 17 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 278 2 16 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 278 (accept_3_2 31 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 278 2 15 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 278 (Polychromatic418967fa.accept_17_12_11_6_1_3729 29 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 278 2 14 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 278 2 13 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 278 (accept_3_2 25 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 278 2 12 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 278 (Polychromatic418967fa.accept_19_4_8_12_1_4757 23 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 278 2 11 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 278 2 10 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 278 (accept_3_2 19 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 278 2 9 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 198 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 278 2 8 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 278 2 7 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 278 (accept_3_2 13 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 278 2 6 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 198 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 278 2 5 99 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 278 2 4 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 278 (accept_3_2 7 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  278 2 3 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 278 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 198 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 278 2 2 99 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 198 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 278 2 1 99 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 278 (accept_3_2 1 198 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 197 278 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 197 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 80
  197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 197 278 (accept_3_2 79
  197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 197 278
  (Polychromatic418967fa.accept_21_15_8_5_1_12668 78 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 197 278 (Polychromatic418967fa.accept_13_12_2_5_1_1634 77 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 197 278 (accept_3_2 76 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 197 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 74 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 197 278 (accept_3_2 73 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 197 278 (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 278 (accept_3_2 70 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 197 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 68 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 197 278 (accept_3_2 67 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 197 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 197 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 197 278 (accept_3_2 64 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 197 278 (accept_3_2 61 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 197 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 278 (accept_3_2 58 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 278 (accept_3_2 55 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 278 (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 278 (accept_3_2 52 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 278
  (Polychromatic418967fa.accept_17_16_10_6_1_7313 50 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 197 278 (accept_3_2 49 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 197 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 197 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 278 (accept_3_2 46 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45
  197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 278 (accept_3_2 43 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 278 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 278 (accept_3_2 40 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 278
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 278 (accept_3_2 37 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 278 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 278 (accept_3_2 34 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 278
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 278 (accept_3_2 31 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 278 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 278 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 278 (accept_3_2 28 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 278
  (Polychromatic418967fa.accept_22_4_21_14_1_9361 26 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 197 278 (accept_3_2 25 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 197 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 197 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 278 (accept_3_2 22 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 278
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 278 (accept_3_2 19 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 278 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 278 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 278 (accept_3_2 16 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 278
  (Polychromatic418967fa.accept_19_14_7_12_1_7732 14 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 197 278 (accept_3_2 13 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 197 278 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 197 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 278 (accept_3_2 10 197 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 278 (accept_3_2 7 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 278 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 278 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 278 (accept_3_2 4 197 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 278
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 278 (accept_3_2 1 197 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 196 278 (Eq.refl
  Bool.true) (allA_of_3_0 83 196 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 195 278 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 195 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 195 278 (accept_3_2 82 195 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 195 278
  (Polychromatic418967fa.accept_19_4_5_12_1_3441 80 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 195 278 (accept_3_2 79 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 195 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 278 (accept_3_2 76 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 195 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 195 278 (accept_3_2 73 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 195 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 278 (accept_3_2 70 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 195 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 195 278 (accept_3_2 67 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 278 (accept_3_2 64 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 278 (accept_3_2 61 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 195 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 278 (accept_3_2 58 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 195 278 (accept_3_2 55 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 195 278 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 278 (accept_3_2 52 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 278 (Polychromatic418967fa.accept_19_13_5_12_1_6107 51 195 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 195 278 (accept_3_2 49 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 278 (accept_3_2 46 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 278
  (Polychromatic418967fa.accept_23_21_11_2_1_17039 44 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 195 278 (accept_3_2 43 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 195 278 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 195 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 195 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 278 (accept_3_2 40 195 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 278 (Polychromatic418967fa.accept_7_4_6_5_1_141
  39 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 278 (accept_3_2 37 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 195 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 278 (accept_3_2 34 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 278 (accept_3_2 31 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 278 (accept_3_2 28 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 278 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 278
  (Polychromatic418967fa.accept_17_9_8_6_1_6050 26 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 278 (accept_3_2 25 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 195 278 (Polychromatic418967fa.accept_21_3_6_5_1_8187 24 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 278 (accept_3_2 22 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 278 (accept_3_2 19 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 278 (accept_3_2 16 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 278
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 278 (accept_3_2 13 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 278 (accept_3_2 10 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 278 (accept_3_2 7 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 278 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 278 (accept_3_2 4 195 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 278
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 278 (accept_3_2 1 195 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 194 278
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 194 278 2 42 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 194 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 194 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 194 278 2 41 97 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 194 278
  (Polychromatic418967fa.accept_11_4_7_3_1_289 81 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 194 278 2 40 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 194 278 (accept_3_2 79 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 194 278 2 39 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 194 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 77 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 194 278 2 38 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 194 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 75 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 194 278 2 37 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 194 278 (accept_3_2 73 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 194 278 2 36 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 194 278 (Polychromatic418967fa.accept_13_6_12_5_1_2304 71 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 194 278 2 35 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 194 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 69 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 194 278 2 34 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 194 278 (accept_3_2 67 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 194 278 2 33 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 194 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 194 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 278 2 32 97 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 278
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 194 278 2 31 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 194 278 (accept_3_2 61 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 278 2 30 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 278 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 194 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 278 2 29 97 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 278 2 28 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 278 (accept_3_2 55 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 278 2 27 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 278 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 278 2 26 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 278 2 25 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 278 (accept_3_2 49 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 278 2 24 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 194 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 278 2 23 97 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 278
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 278 2 22 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 278 (accept_3_2 43 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 278 2 21 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 278 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 278 2 20 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 278 2 19 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 278 (accept_3_2 37 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 278 2 18 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 278 2 17 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 278 2 16 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 278 (accept_3_2 31 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 278 2 15 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 194 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 278 2 14 97 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 278
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 278 2 13 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 278 (accept_3_2 25 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 278 2 12 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 278 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 278 2 11 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 278
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 278 2 10 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 278 (accept_3_2 19 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 278 2 9 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 278 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 278 2 8 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 278
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 278 2 7 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 278 (accept_3_2 13 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 278 2 6 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 278 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 278 2 5 97 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 278
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 278 2 4 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 278 (accept_3_2 7 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  278 2 3 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 278 (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 194 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 278 2 2 97 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 194 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 278 2 1 97 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 278 (accept_3_2 1 194 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 193 278
  (Eq.refl Bool.true) (allA_of_3_0 86 193 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 192 278 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 192 278 2 43 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 192 278 (accept_3_2 85 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 192 278 2 42 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 192 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 192 278 2 41 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 192 278
  (Polychromatic418967fa.accept_21_18_3_5_1_9796 81 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 192 278 2 40 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 192 278 (accept_3_2 79 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 278 2 39 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 192 278 2 38 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 192 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 75 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 192 278 2 37 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 192 278 (accept_3_2 73 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 278 2 36 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 192 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 192 278 2 35 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 192 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 69 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 192 278 2 34 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 192 278 (accept_3_2 67 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 278 2 33 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 192 278 2 32 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 192 278
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 192 278 2 31 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 192 278 (accept_3_2 61 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 278 2 30 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 278 2 29 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 57 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 192 278 2 28 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 192 278 (accept_3_2 55 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 278 2 27 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 278 (Polychromatic418967fa.accept_33_20_27_14_1_17073 53 192 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 278 2 26 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 51 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 192 278 2 25 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 278 (accept_3_2 49 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 278 2 24 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 278 2 23 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 278
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 192 278 2 22 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 192 278 (accept_3_2 43 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 278 2 21 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 278 2 20 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 278
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 39 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 278 2 19 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 278 (accept_3_2 37 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 278 2 18 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 192 278 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 278 2 17 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 278
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 192 278 2 16 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 192 278 (accept_3_2 31 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 192 278 2 15 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 192 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 192 278 2 14 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 192 278
  (Polychromatic418967fa.accept_21_6_3_5_1_8198 27 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 192 278 2 13 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 278 (accept_3_2 25 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 278 2 12 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 278 2 11 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 278
  (Polychromatic418967fa.accept_13_8_10_5_1_977 21 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 278 2 10 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 192 278 (accept_3_2 19 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 278 2 9 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 278 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 192 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 278 2 8 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 278 2 7 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 278 (accept_3_2 13 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 278 2 6 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 278 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 278 2 5 96 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 278 2 4 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 278 (accept_3_2 7 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  278 2 3 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 278 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 278 2 2 96 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 278 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 192 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 278 2 1 96 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 278 (accept_3_2 1 192 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 191 278
  (Eq.refl Bool.true) (allA_succ_of_accept 87 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 191 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 191 278 (accept_3_2 85 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 191 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 191 278 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 191 278 (accept_3_2 82 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 191 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 191 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 191 278 (accept_3_2 79 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 191 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 191 278 (accept_3_2 76 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 191 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 191 278 (accept_3_2 73 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 191 278 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 191 278 (Polychromatic418967fa.accept_16_7_15_6_1_1428 71 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 191 278 (accept_3_2 70 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 191 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 191 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 191 278 (accept_3_2 67 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 191 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 191 278 (accept_3_2 64 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 278
  (Polychromatic418967fa.accept_11_7_4_3_1_302 62 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 191 278 (accept_3_2 61 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 191 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 278 (accept_3_2 58 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 278 (accept_3_2 55 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 278 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 278 (accept_3_2 52 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 278 (accept_3_2 49 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 278 (Polychromatic418967fa.accept_19_9_1_12_1_6234 47 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 278 (accept_3_2 46 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 191 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 278 (accept_3_2 43 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 278 (accept_3_2 40 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 278
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 278 (accept_3_2 37 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 278 (Polychromatic418967fa.accept_17_2_4_6_1_1619 36 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 278 (Polychromatic418967fa.accept_14_7_9_12_1_3975 35 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 278 (accept_3_2 34 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 191 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 278
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 278 (accept_3_2 31 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 278 (accept_3_2 28 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 278
  (Polychromatic418967fa.accept_19_7_1_12_1_6134 26 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 278 (accept_3_2 25 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 278 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 278 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 278 (accept_3_2 22 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 278 (accept_3_2 19 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 278 (accept_3_2 16 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 278
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 278 (accept_3_2 13 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 278 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 278 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 278 (accept_3_2 10 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 278
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 278 (accept_3_2 7 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 278 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 278 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 278 (accept_3_2 4 191 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 278
  (Polychromatic418967fa.accept_13_2_9_5_1_959 2 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 278 (accept_3_2 1 191 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 190 278
  (Eq.refl Bool.true) (allA_of_3_0 89 190 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 189 278 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 278 (accept_3_2 88 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 189 278
  (Polychromatic418967fa.accept_14_2_7_12_1_1485 86 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 189 278 (accept_3_2 85 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 189 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 278 (accept_3_2 82 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 278 (Polychromatic418967fa.accept_10_1_9_8_1_123 81 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 278
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 80 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 189 278 (accept_3_2 79 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 189 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 78 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 278 (accept_3_2 76 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 189 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 74 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 189 278 (accept_3_2 73 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 189 278 (Polychromatic418967fa.accept_14_2_7_12_1_1485 72 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 278 (accept_3_2 70 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 278 (Polychromatic418967fa.accept_17_1_2_6_1_818 69 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 189 278
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 68 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 189 278 (accept_3_2 67 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 189 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 278 (accept_3_2 64 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 278
  (Polychromatic418967fa.accept_15_2_9_8_1_736 62 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 278 (accept_3_2 61 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 189 278 (Polychromatic418967fa.accept_18_6_9_8_1_6812 60 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 278 (accept_3_2 58 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 278 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 278
  (Polychromatic418967fa.accept_11_1_2_3_1_688 56 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 189 278 (accept_3_2 55 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 189 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 278 (accept_3_2 52 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 278
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 278 (accept_3_2 49 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 189 278 (Polychromatic418967fa.accept_15_3_9_8_1_3164 48 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 278 (accept_3_2 46 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 278 (accept_3_2 43 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 189 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 278 (accept_3_2 40 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 278
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 38 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 278 (accept_3_2 37 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 189 278 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 278 (accept_3_2 34 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 278 (Polychromatic418967fa.accept_14_5_7_12_1_4006 33 189 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 278
  (Polychromatic418967fa.accept_15_2_9_8_1_736 32 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 278 (accept_3_2 31 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 189 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 278 (accept_3_2 28 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 278
  (Polychromatic418967fa.accept_19_7_18_12_1_3427 26 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 189 278 (accept_3_2 25 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 189 278 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 189 278 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 278 (accept_3_2 22 189 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 278 (Polychromatic418967fa.accept_10_1_9_8_1_123
  21 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 278
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 20 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 278 (accept_3_2 19 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 278 (accept_3_2 16 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 278
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 278 (accept_3_2 13 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 278 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 278 (accept_3_2 10 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 278 (Polychromatic418967fa.accept_14_9_7_12_1_4034 9 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 278
  (Polychromatic418967fa.accept_23_8_5_2_1_17072 8 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 278 (accept_3_2 7 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 278 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 278 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 278 (accept_3_2 4 189 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 278
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 278 (accept_3_2 1 189 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  278)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 188 278
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 188 278 2 45 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 188 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 188 278 2 44 94 139 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 188 278
  (Polychromatic418967fa.accept_17_2_1_6_1_3777 87 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 188 278 2 43 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 188 278 (accept_3_2 85 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 188 278 2 42 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 188 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 83 188 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 188 278 2 41 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 188 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 81 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 188 278 2 40 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 188 278 (accept_3_2 79 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 188 278 2 39 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 188 278 2 38 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 188 278
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 188 278 2 37 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 188 278 (accept_3_2 73 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 188 278 2 36 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 188 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 278 2 35 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 278
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 69 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 278 2 34 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 278 (accept_3_2 67 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 278 2 33 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 278 2 32 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 278
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 188 278 2 31 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 188 278 (accept_3_2 61 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 278 2 30 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 188 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 278 2 29 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 278 2 28 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 278 (accept_3_2 55 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 278 2 27 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 278 2 26 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 278
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 278 2 25 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 278 (accept_3_2 49 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 278 2 24 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 188 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 278 2 23 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 278
  (Polychromatic418967fa.accept_27_18_26_8_1_7479 45 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 188 278 2 22 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 188 278 (accept_3_2 43 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 278 2 21 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 278 2 20 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 278
  (Polychromatic418967fa.accept_7_4_6_5_1_141 39 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 278 2 19 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 278 (accept_3_2 37 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 278 2 18 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 188 278 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 278 2 17 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 278
  (Polychromatic418967fa.accept_19_14_17_12_1_6099 33 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 188 278 2 16 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 188 278 (accept_3_2 31 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 188 278 2 15 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 278 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 278 2 14 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 278
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 27 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 188 278 2 13 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 188 278 (accept_3_2 25 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 278 2 12 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 278 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 188 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 278 2 11 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 278
  (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 188 278 2 10 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 188 278 (accept_3_2 19 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 278 2 9 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 278 2 8 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 278
  (Polychromatic418967fa.accept_7_1_6_5_1_39 15 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 278 2 7 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 278 (accept_3_2 13 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 278 2 6 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 278 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 188 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 278 2 5 94 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 278
  (Polychromatic418967fa.accept_23_9_4_2_1_17071 9 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 278 2 4 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 278 (accept_3_2 7 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  278 2 3 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 278 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 188 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 278 2 2 94 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 278 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 188 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 278 2 1 94 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 278 (accept_3_2 1 188 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 187 278
  (Eq.refl Bool.true) (allA_of_3_0 92 187 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 186 278 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 186 278 2 46 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 186 278 (accept_3_2 91 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 186 278 2 45 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 278 (Polychromatic418967fa.accept_15_14_6_8_1_1410 89 186 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 186 278 2 44 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 186 278
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 186 278 2 43 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 186 278 (accept_3_2 85 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 186 278 2 42 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 186 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 83 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 186 278 2 41 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 186 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 186 278 2 40 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 186 278 (accept_3_2 79 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 186 278 2 39 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 186 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 186 278 2 38 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 186 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 75 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 186 278 2 37 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 186 278 (accept_3_2 73 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 186 278 2 36 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 186 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 186 278 2 35 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 186 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 186 278 2 34 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 186 278 (accept_3_2 67 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 278 2 33 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 278 2 32 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 186 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 186 278 2 31 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 186 278 (accept_3_2 61 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 278 2 30 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 278 2 29 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 186 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 186 278 2 28 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 186 278 (accept_3_2 55 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 278 2 27 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 278 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 186 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 278 2 26 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 278 2 25 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 278 (accept_3_2 49 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 278 2 24 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 278 2 23 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 278
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 278 2 22 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 278 (accept_3_2 43 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 278 2 21 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 278 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 278 2 20 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 278 2 19 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 278 (accept_3_2 37 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 278 2 18 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 278 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 186 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 278 2 17 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 278
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 278 2 16 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 278 (accept_3_2 31 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 278 2 15 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 278 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 278 2 14 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 278
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 278 2 13 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 278 (accept_3_2 25 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 278 2 12 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 278 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 278 2 11 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 278
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 278 2 10 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 278 (accept_3_2 19 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 278 2 9 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 278 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 278 2 8 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 278
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 278 2 7 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 278 (accept_3_2 13 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 278 2 6 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 278 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 278 2 5 93 139 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 278
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 278 2 4 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 278 (accept_3_2 7 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  278 2 3 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 278 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 186 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 278 2 2 93 139 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 278 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 278 2 1 93 139 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 278 (accept_3_2 1 186 278
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 185
  278 (Eq.refl Bool.true) (allA_succ_of_accept 93 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 185 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 92 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 185 278 (accept_3_2 91 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 185 278 (Polychromatic418967fa.accept_20_10_5_18_1_5627 90 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 185 278 (Polychromatic418967fa.accept_13_11_3_5_1_982 89 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 185 278 (accept_3_2 88 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 185 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 185 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 86 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 185 278 (accept_3_2 85 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 185 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 185 278 (accept_3_2 82 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 185 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 80 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 185 278 (accept_3_2 79 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 185 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 78 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 185 278 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 185 278 (accept_3_2 76 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 185 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 185 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 185 278 (accept_3_2 73 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 185 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 185 278 (accept_3_2 70 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 278
  (Polychromatic418967fa.accept_12_8_5_2_1_746 68 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 185 278 (accept_3_2 67 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 185 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 185 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 185 278 (accept_3_2 64 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 185 278 (accept_3_2 61 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 185 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 185 278 (accept_3_2 58 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 185 278 (accept_3_2 55 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 185 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 185 278 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 278 (accept_3_2 52 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 185 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 50 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 278 (accept_3_2 49 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 278 (accept_3_2 46 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 44 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 278 (accept_3_2 43 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 278 (Polychromatic418967fa.accept_13_2_3_5_1_2294 41 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 278 (accept_3_2 40 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 185 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 278 (accept_3_2 37 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 278 (accept_3_2 34 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 278
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 278 (accept_3_2 31 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 278 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 278 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 278 (accept_3_2 28 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 278
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 278 (accept_3_2 25 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 278 (accept_3_2 22 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 278
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 278 (accept_3_2 19 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 278 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 278 (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 278 (accept_3_2 16 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 278
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 278
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 278 (accept_3_2 13 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 278 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 278 (accept_3_2 10 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 278 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 278
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 278 (accept_3_2 7 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 278 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 278 (Polychromatic418967fa.accept_14_5_3_12_1_324 5 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 278 (accept_3_2 4 185 278 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 278 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 278 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 278
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 278 (accept_3_2 1 185 278 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  278))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_278_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


