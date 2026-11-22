-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch272
-- name    : Polychromatic418967fa_Branch272
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:33:25.381976+00:00
-- url     : https://prove2.me/theorems/e3cb945b-a8ea-449d-8d2f-ca46e66e40c2
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch272_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_272 : allB 272 272 :=
  allB_succ' 2 271 272 (Eq.refl Bool.true) (allA_of_3_0 2 271 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  270 272 (Eq.refl Bool.true) (allA_succ_of_gcd 2 270 272 2 1 135 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 272 (accept_3_2 1 270 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 270 272))) (allB_succ' 4 269 272 (Eq.refl Bool.true) (allA_succ_of_accept 3 269 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 269 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 269 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 269 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 272 (accept_3_2 1 269 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 269 272)))) (allB_succ' 5 268 272 (Eq.refl Bool.true) (allA_of_3_0 5 268 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 267 272 (Eq.refl Bool.true) (allA_succ_of_accept 5 267 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 267 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 267 272 (accept_3_2 4 267 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  267 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 267 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 267 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 267 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 272 (accept_3_2 1 267 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 267 272)))))) (allB_succ' 7 266 272 (Eq.refl Bool.true) (allA_succ_of_gcd 6 266 272 2 3
  133 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 266 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 266 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 266 272 2 2 133 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 266 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 266 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 266 272 2 1 133 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 266 272 (accept_3_2 1 266 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 266 272))))))) (allB_succ' 8 265 272 (Eq.refl Bool.true) (allA_of_3_0 8 265
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 264 272 (Eq.refl Bool.true) (allA_succ_of_gcd 8 264 272 8 1
  33 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 264 272
  (accept_3_2 7 264 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264 272 2 3 132 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 264 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 264 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 264 272 4 1 66 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 264 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 264 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 264 272 2 1 132 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 272 (accept_3_2 1 264 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 264 272))))))))) (allB_succ' 10 263 272 (Eq.refl Bool.true) (allA_succ_of_accept 9 263
  272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 263 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 263 272 (Polychromatic418967fa.accept_19_8_16_6_1_5804 8 263 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 272 (accept_3_2 7 263 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 263 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 263 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  263 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 272 (accept_3_2 4 263
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 263 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 263 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 263 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 263 272 (accept_3_2 1 263 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263
  272)))))))))) (allB_succ' 11 262 272 (Eq.refl Bool.true) (allA_of_3_0 11 262 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 261 272 (Eq.refl Bool.true) (allA_succ_of_accept 11 261 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 261 272 (accept_3_2 10 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  261 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 261 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 261 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 272 (accept_3_2 7 261 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 261 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 261 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 261 272 (accept_3_2 4 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  261 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 261 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 261 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 261 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 272 (accept_3_2 1 261 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 261 272)))))))))))) (allB_succ' 13 260 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 260 272 4 3 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 260 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 260 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 260 272 2 5 130 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 260 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  260 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 260 272 4 2 65 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 260 272 (accept_3_2 7
  260 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 260 272 2 3 130 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 260 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 260 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 260 272 4 1 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 260 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 260 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 260 272 2 1 130 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 260 272 (accept_3_2 1 260 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 260 272))))))))))))) (allB_succ' 14 259 272 (Eq.refl Bool.true) (allA_of_3_0 14 259 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 258 272 (Eq.refl Bool.true) (allA_succ_of_gcd 14 258 272 2 7
  129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 258
  272 (accept_3_2 13 258 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 258 272 2 6 129 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 258 272
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 258 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 258 272 2 5 129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 258 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 258 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 258 272 2 4 129 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 272 (accept_3_2 7 258 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 258 272 2 3 129 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 258 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 258 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 258 272 2 2 129 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 258 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 258 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 258 272 2 1 129 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 272 (accept_3_2 1 258 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 258 272))))))))))))))) (allB_succ' 16 257 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 257 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 257 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 257 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 257
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 272 (accept_3_2 13 257
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 257 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 257 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 257 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 257 272 (accept_3_2 10 257 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 257 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 257 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 257 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8
  257 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 272 (accept_3_2 7 257
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 257 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 257 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 257 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 272 (accept_3_2 4 257 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 257 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 257 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  257 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 272 (accept_3_2 1 257
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257 272)))))))))))))))) (allB_succ' 17 256 272 (Eq.refl
  Bool.true) (allA_of_3_0 17 256 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 255 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 17 255 272 17 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 16 255 272 (accept_3_2 16 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 255 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 255 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 255 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 255 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 272 (accept_3_2 13 255 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 255 272 (Polychromatic418967fa.accept_18_12_3_2_1_756
  12 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 255 272 (accept_3_2 10 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  255 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 255 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 255 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 272 (accept_3_2 7 255 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 255 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 255 272 (accept_3_2 4 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  255 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 255 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 255 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 255 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 272 (accept_3_2 1 255 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 255 272)))))))))))))))))) (allB_succ' 19 254 272 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 254 272 2 9 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 254 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 254 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 254 272 2 8 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 254 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  254 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 254 272 2 7 127 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 254 272 (accept_3_2 13
  254 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 254 272 2 6 127 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 254 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 254 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 254 272 2 5 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 254 272 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 254 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 254 272 2 4 127 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 254 272 (accept_3_2 7 254 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 254 272 2 3 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 254 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5
  254 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 254 272 2 2 127 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 254 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 254 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 254 272 2 1 127 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 254 272 (accept_3_2 1 254 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  272))))))))))))))))))) (allB_succ' 20 253 272 (Eq.refl Bool.true) (allA_of_3_0 20 253 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 252 272 (Eq.refl Bool.true) (allA_succ_of_gcd 20 252 272 4 5 63 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 252 272 (accept_3_2 19 252 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 252 272 2 9 126 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 252 272
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 252 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 252 272 4 4 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 252 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 252 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 272 2 7 126 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 272 (accept_3_2 13 252 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 252 272 4 3 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 252 272 (Polychromatic418967fa.accept_19_11_5_6_1_7183 11 252
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 252 272 2 5 126 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 252 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 252 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 252 272 4 2 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 252 272 (accept_3_2 7 252 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252
  272 2 3 126 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  252 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 252 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 252 272 4 1 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 252 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 252 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 272 2 1 126 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 272 (accept_3_2 1 252 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 252 272))))))))))))))))))))) (allB_succ' 22 251 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 251 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 251 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 251 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 251
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 272 (accept_3_2 19 251
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 272
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 251 272 (Polychromatic418967fa.accept_19_17_4_6_1_5810 17 251 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 272 (accept_3_2 16 251 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 251 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 251 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 272 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 272 (accept_3_2 13
  251 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 251 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 251 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 272 (accept_3_2 10 251 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 251 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 272
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 251 272 (accept_3_2 7 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  251 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 251 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 251 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 272 (accept_3_2 4 251 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 251 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 272 (accept_3_2 1 251 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  272)))))))))))))))))))))) (allB_succ' 23 250 272 (Eq.refl Bool.true) (allA_of_3_0 23 250 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 249 272 (Eq.refl Bool.true) (allA_succ_of_accept 23 249 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 272 (accept_3_2 22 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 249 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 249 272 (Polychromatic418967fa.accept_19_1_2_6_1_4411 20 249 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 272 (accept_3_2 19 249 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 249
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 272 (accept_3_2 16 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 249 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 249 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 272 (accept_3_2 13 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 249 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 272 (accept_3_2 10 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  249 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 249 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 272 (accept_3_2 7 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 249 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 272 (accept_3_2 4 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 249 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 272 (accept_3_2 1 249 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 272)))))))))))))))))))))))) (allB_succ' 25 248 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 248 272 8 3 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 248 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 248 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 248 272 2 11 124 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 248 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  248 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 248 272 4 5 62 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 248 272 (accept_3_2 19
  248 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 248 272 2 9 124 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 248 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 248 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 248 272 8 2 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 248 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 248 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 248 272 2 7 124 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 248 272 (accept_3_2 13 248 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 248 272 4 3 62 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 248 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 248 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 248 272 2 5 124 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 248 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 248 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 248 272 8 1 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 248 272 (accept_3_2 7 248 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 248
  272 2 3 124 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  248 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 248 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 248 272 4 1 62 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 248 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 248 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 248 272 2 1 124 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 248 272 (accept_3_2 1 248 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 248 272))))))))))))))))))))))))) (allB_succ' 26 247 272 (Eq.refl Bool.true)
  (allA_of_3_0 26 247 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 246 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 246 272 2 13 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 246 272 (accept_3_2 25 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 246 272 2 12 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 246 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 246 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 246 272 2 11 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 246 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 246 272 2 10 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 246 272 (accept_3_2 19 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 272 2 9 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 246 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 246 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 272 2 8 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 246 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 246 272 2 7 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 246 272 (accept_3_2 13 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 272 2 6 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 246 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 272 2 5 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 246 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 246 272 2 4 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 246 272 (accept_3_2 7 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 272 2 3 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 246 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 272 2 2 123 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 246 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 246 272 2 1 123 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 246 272 (accept_3_2 1 246 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  272))))))))))))))))))))))))))) (allB_succ' 28 245 272 (Eq.refl Bool.true) (allA_succ_of_accept 27 245 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 245 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 245 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 245 272 (accept_3_2 25 245 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 245 272 (Polychromatic418967fa.accept_23_1_15_19_1_11864 24 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 272
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 245 272 (accept_3_2 22 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 245 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 245 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 245 272 (accept_3_2 19 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 245
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 272
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 245 272 (accept_3_2 16 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 245 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 245 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 272 (accept_3_2 13 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 12 245
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 245 272 (accept_3_2 10 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  245 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 245 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 245 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 272 (accept_3_2 7 245 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 245 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 272 (accept_3_2 4 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 245 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 245 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 272 (accept_3_2 1 245 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 272)))))))))))))))))))))))))))) (allB_succ' 29 244 272 (Eq.refl Bool.true)
  (allA_of_3_0 29 244 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 243 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 243 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 243 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 272 (accept_3_2 28 243 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 243 272 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 243 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 272
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 272 (accept_3_2 25 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 272 (accept_3_2 22 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 243 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 272
  (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 272 (accept_3_2 19 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 272 (accept_3_2 16 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 243 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 272
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 272 (accept_3_2 13 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 272 (accept_3_2 10 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 272 (Polychromatic418967fa.accept_19_9_15_6_1_4396 9 243 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 272 (accept_3_2 7 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 272 (accept_3_2 4 243 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 243 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 272
  (Polychromatic418967fa.accept_19_2_15_6_1_4408 2 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 272 (accept_3_2 1 243 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  272)))))))))))))))))))))))))))))) (allB_succ' 31 242 272 (Eq.refl Bool.true) (allA_succ_of_gcd 30 242 272 2 15 121 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 242 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 242 272 2 14 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 242 272 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 242 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 242 272 2 13 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 242 272 (accept_3_2 25 242 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 242 272 2 12 121 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 242 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 242 272 2 11 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 242 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 242 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 242 272 2 10 121 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 242 272 (accept_3_2 19 242 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 242 272 2 9 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 242 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 272 2 8 121 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 272 2 7 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 272 (accept_3_2 13 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 272 2 6 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 242 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 272 2 5 121 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 272 2 4 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 272 (accept_3_2 7 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 272 2 3 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 242 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 272 2 2 121 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 272 2 1 121 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 272 (accept_3_2 1 242 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  272))))))))))))))))))))))))))))))) (allB_succ' 32 241 272 (Eq.refl Bool.true) (allA_of_3_0 32 241 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 240 272 (Eq.refl Bool.true) (allA_succ_of_gcd 32 240 272 16 2 15 17
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 240 272
  (accept_3_2 31 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 240 272 2 15 120 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 240 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 240 272 4 7 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 240 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 240 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 272 2 13 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 240 272 (accept_3_2 25 240 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 240 272 8 3 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 240 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 240 272 2 11 120 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 240 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 240 272 4 5 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 240 272 (accept_3_2 19 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  240 272 2 9 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 240 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 240 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 240 272 16 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 240 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  240 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 240 272 2 7 120 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 240 272 (accept_3_2 13
  240 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 272 4 3 60 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 240 272 2 5 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 240 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 240 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 272 8 1 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 272 (accept_3_2 7 240 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 272 2 3 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 240 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 272 4 1 60 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 240 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 240 272 2 1 120 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 240 272 (accept_3_2 1 240 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  272))))))))))))))))))))))))))))))))) (allB_succ' 34 239 272 (Eq.refl Bool.true) (allA_succ_of_accept 33 239 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 239 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 32 239 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 239 272 (accept_3_2 31 239 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 239 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 239 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 239 272
  (Polychromatic418967fa.accept_20_9_19_12_1_5221 29 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 239 272 (accept_3_2 28 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 239 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 239 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 239 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 239 272 (accept_3_2 25 239 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 239 272 (Polychromatic418967fa.accept_9_6_5_2_1_421
  24 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 239 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 239 272 (accept_3_2 22 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 239 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 239 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 239 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 272 (accept_3_2 19 239 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 239 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 239
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 239 272 (accept_3_2 16 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 239 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 239 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 239 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 272 (accept_3_2 13 239 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 239 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 239 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 272 (accept_3_2 10 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 239 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 272 (accept_3_2 7 239 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 239 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 272 (accept_3_2 4 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 239 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 272 (accept_3_2 1 239 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 272)))))))))))))))))))))))))))))))))) (allB_succ' 35 238 272 (Eq.refl Bool.true)
  (allA_of_3_0 35 238 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 237 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 237 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 272 (accept_3_2 34 237 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 237 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 272 (Polychromatic418967fa.accept_9_5_3_2_1_171
  32 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 272 (accept_3_2 31
  237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 237 272
  (Polychromatic418967fa.accept_12_6_9_8_1_165 30 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 237 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 272 (accept_3_2 28 237 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 237 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 27 237 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 272 (accept_3_2 25 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 272 (accept_3_2 22 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 272 (Polychromatic418967fa.accept_14_7_13_6_1_1177 21 237 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 272
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 272 (accept_3_2 19 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 272 (accept_3_2 16 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 237 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 272 (accept_3_2 13 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 272 (accept_3_2 10 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 237 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 272 (accept_3_2 7 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 272 (accept_3_2 4 237 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 237 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 272
  (Polychromatic418967fa.accept_13_2_3_12_1_735 2 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 272 (accept_3_2 1 237 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  272)))))))))))))))))))))))))))))))))))) (allB_succ' 37 236 272 (Eq.refl Bool.true) (allA_succ_of_gcd 36 236 272 4 9 59
  68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 236 272
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 236 272 2 17 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 236 272 (Polychromatic418967fa.accept_19_14_8_6_1_981 33 236 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 236 272 4 8 59 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 236 272 (accept_3_2 31 236 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 236 272 2 15 118 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 236 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 236 272 4 7 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 236 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 236 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 236 272 2 13 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 236 272 (accept_3_2 25 236 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 236 272 4 6 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 236 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 236
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 236 272 2 11 118 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 236 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 236 272 4 5 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 236 272 (accept_3_2 19 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  236 272 2 9 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 236 272 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 236 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 272 4 4 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 236 272 2 7 118 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 236 272 (accept_3_2 13
  236 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 236 272 4 3 59 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 236 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 236 272 2 5 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 236 272 (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 236 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 272 4 2 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 272 (accept_3_2 7 236 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 272 2 3 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 236 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 272 4 1 59 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 272
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 272 2 1 118 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 272 (accept_3_2 1 236 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  272))))))))))))))))))))))))))))))))))))) (allB_succ' 38 235 272 (Eq.refl Bool.true) (allA_of_3_0 38 235 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 234 272 (Eq.refl Bool.true) (allA_succ_of_gcd 38 234 272 2 19 117 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 234 272
  (accept_3_2 37 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 234 272 2 18 117 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 234 272
  (Polychromatic418967fa.accept_24_11_18_8_1_16695 35 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 234 272 2 17 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 234 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 234 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 234 272 2 16 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 272 (accept_3_2 31 234 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 234 272 2 15 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 234 272
  (Polychromatic418967fa.accept_25_4_9_22_1_16659 29 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 234 272 2 14 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 234 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 234 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 234 272 2 13 117 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 272 (accept_3_2 25 234 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 234 272 2 12 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 234 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 234 272 2 11 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 234 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 234 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 272 2 10 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 272 (accept_3_2 19 234 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 234 272 2 9 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 272 (Polychromatic418967fa.accept_10_7_4_2_1_903
  17 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 272 2 8 117 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 234 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 234 272 2 7 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 234 272 (accept_3_2 13 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 272 2 6 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 234 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 272 2 5 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 234 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 234 272 2 4 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 234 272 (accept_3_2 7 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 272 2 3 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 234 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 272 2 2 117 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 234 272 2 1 117 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 234 272 (accept_3_2 1 234 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  272))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 233 272 (Eq.refl Bool.true) (allA_succ_of_accept 39 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 233 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 233 272 (accept_3_2 37 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 233 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 272 (Polychromatic418967fa.accept_10_5_3_2_1_899
  35 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 233 272 (accept_3_2 34
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 233 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 272 (accept_3_2 31 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 233 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 233 272 (accept_3_2 28
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 233 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 272 (accept_3_2 25 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 233 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 272 (Polychromatic418967fa.accept_9_5_8_2_1_409
  23 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 272 (accept_3_2 22
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 233 272 (Polychromatic418967fa.accept_19_1_5_6_1_5811 20 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 272 (accept_3_2 19 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 233 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 272 (accept_3_2 16
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 233 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 272 (accept_3_2 13 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 233 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 272 (Polychromatic418967fa.accept_7_4_2_6_1_337
  11 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 272 (accept_3_2 10
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 233 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 272 (accept_3_2 7 233 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 233 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 233 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 272 (accept_3_2 4 233
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 272 (accept_3_2 1 233 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  272)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 232 272 (Eq.refl Bool.true) (allA_of_3_0 41 232 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 231 272 (Eq.refl Bool.true) (allA_succ_of_accept 41 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 231 272 (accept_3_2 40 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 231 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 231 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 231 272 (accept_3_2 37 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 231 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 231
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 231 272 (accept_3_2 34 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 231 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 231 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 231 272 (accept_3_2 31 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 231 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 231 272 (accept_3_2 28 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 231 272 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 231 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 272 (accept_3_2 25 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 231 272 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 231 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 231 272 (accept_3_2 22 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 231 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 231 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 272 (accept_3_2 19 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 231 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 231
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 231 272 (accept_3_2 16 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 231 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 231 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 272 (accept_3_2 13 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 231 272 (accept_3_2 10 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  231 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 231 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 272 (accept_3_2 7 231 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 272 (accept_3_2 4 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  231 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 231 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 231 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 272 (accept_3_2 1 231 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 272)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 230 272
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 230 272 2 21 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 230 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 230 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 230 272 2 20 115 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 230 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 230 272 2 19 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 230 272 (accept_3_2 37 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 230 272 2 18 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 230 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 230 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 230 272 2 17 115 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 230 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 230 272 2 16 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 230 272 (accept_3_2 31 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 230 272 2 15 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 230 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 230 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 230 272 2 14 115 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 230 272
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 230 272 2 13 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 230 272 (accept_3_2 25 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 230 272 2 12 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 230 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 230 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 230 272 2 11 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 230 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 230 272 2 10 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 230 272 (accept_3_2 19 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 230 272 2 9 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 230 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 230 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 272 2 8 115 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 272 2 7 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 272 (accept_3_2 13 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 272 2 6 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 230 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 272 2 5 115 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 272 2 4 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 272 (accept_3_2 7 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 272 2 3 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 230 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 272 2 2 115 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 272 2 1 115 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 272 (accept_3_2 1 230 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  272))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 229 272 (Eq.refl Bool.true) (allA_of_3_0 44 229 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 228 272 (Eq.refl Bool.true) (allA_succ_of_gcd 44 228 272 4 11
  57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 228 272
  (accept_3_2 43 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 228 272 2 21 114 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 228 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 228 272 4 10 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 228 272 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 228 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 228 272 2 19 114 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 228 272 (accept_3_2 37 228 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 228 272 4 9 57 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 228 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 228 272 2 17 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 228 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 228 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 272 4 8 57 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 272 (accept_3_2 31 228 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 272 2 15 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811
  29 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 272 4 7 57 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 228 272
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 228 272 2 13 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 228 272 (accept_3_2 25 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 272 4 6 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 228 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 228 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 272 2 11 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 272 (Polychromatic418967fa.accept_13_8_7_12_1_3637
  21 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 228 272 4 5 57 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 272
  (accept_3_2 19 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 272 2 9 114 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 228 272 4 4 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 228 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 228 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 272 2 7 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 272 (accept_3_2 13 228 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 272 4 3 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 228
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 272 2 5 114 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 228 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 228 272 4 2 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 228 272 (accept_3_2 7 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228
  272 2 3 114 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  228 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 228 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 228 272 4 1 57 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 228 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 228 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 228 272 2 1 114 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 272 (accept_3_2 1 228 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 228 272))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 227 272
  (Eq.refl Bool.true) (allA_succ_of_accept 45 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 227 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 227 272 (accept_3_2 43 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 227 272 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 227 272 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 227 272 (accept_3_2 40 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 227 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 227 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 227 272 (accept_3_2 37 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 227 272 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 227 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 272 (accept_3_2 34 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 227 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 227 272 (accept_3_2 31 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 227 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 227 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 272 (accept_3_2 28 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 227 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 272
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 272 (accept_3_2 25 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 227 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 272 (accept_3_2 22 227 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 272
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 272 (accept_3_2 19 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 272 (accept_3_2 16 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 272 (accept_3_2 13 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 272 (Polychromatic418967fa.accept_19_12_18_6_1_14021 12 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 272 (accept_3_2 10 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 227 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 272
  (Polychromatic418967fa.accept_21_8_17_20_1_3142 8 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 272 (accept_3_2 7 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 272 (Polychromatic418967fa.accept_20_6_7_12_1_8197 6 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 227 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 272 (accept_3_2 4 227 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 272 (accept_3_2 1 227 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  272)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 226 272 (Eq.refl Bool.true) (allA_of_3_0 47 226 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 225 272 (Eq.refl Bool.true) (allA_succ_of_accept 47 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 225 272 (accept_3_2 46 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 225 272 (Polychromatic418967fa.accept_19_7_16_6_1_4400 45 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 225 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 272 (accept_3_2 43 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 225 272 (accept_3_2 40 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 225 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 225 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 272 (accept_3_2 37 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 225
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 225 272 (accept_3_2 34 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 225 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 225 272 (Polychromatic418967fa.accept_22_10_5_8_1_8954 32 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 272 (accept_3_2 31 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 225 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 225 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 225 272 (accept_3_2 28 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 225 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 225 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 272 (accept_3_2 25 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 272 (accept_3_2 22 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 225 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 225 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 272 (accept_3_2 19 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 225
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 225 272 (accept_3_2 16 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 225 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 15 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 225 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 272 (accept_3_2 13 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 225 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 272 (accept_3_2 10 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  225 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 272 (accept_3_2 7 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 225 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 272 (accept_3_2 4 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 225 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 272 (accept_3_2 1 225 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 225 272)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 224 272 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 224 272 16 3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 224 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 224 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 224 272 2 23 112 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 224 272
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 224 272 4 11 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 224 272 (accept_3_2 43 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 224 272 2 21 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 224 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 224 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 224 272 8 5 28 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 224 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 224 272 2 19 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 224 272 (accept_3_2 37 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 224 272 4 9 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 224 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 224 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 224 272 2 17 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 224 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 224 272 16 2 14 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 224 272 (accept_3_2 31
  224 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 224 272 2 15 112 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 224 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 224 272 4 7 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 224 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 224 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 224 272 2 13 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 224 272 (accept_3_2 25 224 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 224 272 8 3 28 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 224 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 272 2 11 112 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 272 4 5 56 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 224 272 (accept_3_2 19 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  224 272 2 9 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 224 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 224 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 272 16 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 224 272 2 7 112 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 224 272 (accept_3_2 13
  224 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 224 272 4 3 56 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 224 272
  (Polychromatic418967fa.accept_19_11_15_6_1_7173 11 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 224 272 2 5 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 224 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 224 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 272 8 1 28 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 224 272 (accept_3_2 7 224 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 224 272 2 3 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 272 4 1 56 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 272 2 1 112 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 272 (accept_3_2 1 224 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  272))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 223 272 (Eq.refl Bool.true) (allA_of_3_0 50 223
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 222 272 (Eq.refl Bool.true) (allA_succ_of_gcd 50 222 272 2
  25 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 222
  272 (accept_3_2 49 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 222 272 2 24 111 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 222 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 47 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 222 272 2 23 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 222 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 222 272 2 22 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 272 (accept_3_2 43 222 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 222 272 2 21 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 222 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41
  222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 222 272 2 20 111 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 222 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 222 272 2 19 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 222 272 (accept_3_2 37 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 272 2 18 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 272 2 17 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 222 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 222 272 2 16 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 222 272 (accept_3_2 31 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 272 2 15 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 272 2 14 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 222 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 222 272 2 13 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 222 272 (accept_3_2 25 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 272 2 12 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 272 2 11 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 272 2 10 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 272 (accept_3_2 19 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 272 2 9 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 272 2 8 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 272 2 7 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 272 (accept_3_2 13 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 272 2 6 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 272 2 5 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 272 2 4 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 272 (accept_3_2 7 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 272 2 3 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 222 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 272 2 2 111 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 272 2 1 111 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 272 (accept_3_2 1 222 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  272))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 221 272 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  221 272 17 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 221 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 221 272 (accept_3_2 49 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 221 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 272 (Polychromatic418967fa.accept_7_5_4_6_1_167
  47 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 221 272 (accept_3_2 46
  221 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 221 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 221 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 272 (accept_3_2 43 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 221 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 272
  (Polychromatic418967fa.accept_23_18_14_19_1_3436 41 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 221 272 (accept_3_2 40 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 221 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 221 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 272 (accept_3_2 37 221 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 272 (Polychromatic418967fa.accept_10_6_1_2_1_874
  36 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 221 272 17 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 221 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 272
  (Polychromatic418967fa.accept_19_13_12_6_1_11362 32 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 221 272 (accept_3_2 31 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 221 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 221
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 272 (accept_3_2 28 221
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 221 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 272 (accept_3_2 25 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 221 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 272 (Polychromatic418967fa.accept_7_2_4_6_1_166
  23 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 272 (accept_3_2 22
  221 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 221 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 272 (accept_3_2 19 221 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 221 272 (Polychromatic418967fa.accept_19_18_12_6_1_7187 18 221 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 221 272 17 1 13 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 221 272 (accept_3_2 16 221 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 272 (accept_3_2 13 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 272 (Polychromatic418967fa.accept_20_11_1_12_1_3803 11 221 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 272 (accept_3_2 10 221 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 272 (accept_3_2 7 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 272 (accept_3_2 4 221 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 272 (accept_3_2 1 221 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  272)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 220 272 (Eq.refl Bool.true) (allA_of_3_0 53 220
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 219 272 (Eq.refl Bool.true) (allA_succ_of_accept 53 219
  272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 219 272 (accept_3_2 52 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 219 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 219 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 272 (accept_3_2 49 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 219 272 (accept_3_2 46 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 219 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 219 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 272 (accept_3_2 43 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 219 272 (accept_3_2 40 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 219 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 272 (accept_3_2 37 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 272 (accept_3_2 34 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 219 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 219 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 272 (accept_3_2 31 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 272 (accept_3_2 28 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 272 (accept_3_2 25 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 272 (accept_3_2 22 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 272 (accept_3_2 19 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 219 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 272 (accept_3_2 16 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 272 (accept_3_2 13 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 272 (accept_3_2 10 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  219 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 219 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 272 (accept_3_2 7 219 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 272 (accept_3_2 4 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 272 (Polychromatic418967fa.accept_19_2_10_6_1_4373 2 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 272 (accept_3_2 1 219 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 272)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55
  218 272 (Eq.refl Bool.true) (allA_succ_of_gcd 54 218 272 2 27 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 218 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 218 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 218 272 2 26 109 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 218 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 218 272 2 25 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 218 272 (accept_3_2 49 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 218 272 2 24 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 218 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 218 272 2 23 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 218 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 218 272 2 22 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 218 272 (accept_3_2 43 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 218 272 2 21 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 218 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 218 272 2 20 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 272
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 272 2 19 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 272 (accept_3_2 37 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 272 2 18 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 272 2 17 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 218 272 2 16 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 218 272 (accept_3_2 31 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 272 2 15 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 272 2 14 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 272
  (Polychromatic418967fa.accept_24_3_2_8_1_4572 27 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 272 2 13 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 272 (accept_3_2 25 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 272 2 12 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 272 2 11 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 272 2 10 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 272 (accept_3_2 19 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 272 2 9 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 272 2 8 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 272 2 7 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 272 (accept_3_2 13 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 272 2 6 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 218 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 272 2 5 109 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 272 2 4 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 272 (accept_3_2 7 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 272 2 3 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 218 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 272 2 2 109 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 272
  (Polychromatic418967fa.accept_19_3_9_6_1_12696 3 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 272 2 1 109 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 272 (accept_3_2 1 218 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 217 272 (Eq.refl Bool.true) (allA_of_3_0 56
  217 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 216 272 (Eq.refl Bool.true) (allA_succ_of_gcd 56 216
  272 8 7 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  216 272 (accept_3_2 55 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 216 272 2 27 108 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 216 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 216 272 4 13 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 216 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 51 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 216 272 2 25 108 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 216 272 (accept_3_2 49 216 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 216 272 8 6 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 216 272
  (Polychromatic418967fa.accept_21_5_6_20_1_16667 47 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 216 272 2 23 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 216 272 (Polychromatic418967fa.accept_21_3_6_20_1_9278 45 216 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 216 272 4 11 54 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 272 (accept_3_2 43 216 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 216 272 2 21 108 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 216 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 216 272 8 5 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 216 272 (Polychromatic418967fa.accept_19_1_7_6_1_1959 39 216 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 216 272 2 19 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 272 (accept_3_2 37 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 272 4 9 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 216
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 272 2 17 108 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 272
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 216 272 8 4 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 216 272 (accept_3_2 31 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  216 272 2 15 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 216 272 (Polychromatic418967fa.accept_22_7_18_8_1_13589 29 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 272 4 7 54 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 216 272 2 13 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 216 272 (accept_3_2 25 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 272 8 3 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 272 (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 272 2 11 108 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 216 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 216 272 4 5 54 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 216 272 (accept_3_2 19 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  216 272 2 9 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 216 272 (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 216 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 272 8 2 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926
  15 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 272 2 7 108 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 272
  (accept_3_2 13 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 272 4 3 54 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 216 272 2 5 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 216 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 272 8 1 27 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 272 (accept_3_2 7 216 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 272 2 3 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 272 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 216 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 272 4 1 54 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 272
  (Polychromatic418967fa.accept_19_3_7_6_1_5791 3 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 272 2 1 108 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 272 (accept_3_2 1 216 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 215 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 215 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 215
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 215 272 (accept_3_2 55 215
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 215 272
  (Polychromatic418967fa.accept_26_2_7_12_1_13077 54 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 215 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 215 272 (accept_3_2 52 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 215 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 215 272 (accept_3_2 49 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 215 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 215 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 272 (accept_3_2 46 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 215 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 215 272
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 215 272 (accept_3_2 43 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 215 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 215 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 215 272 (accept_3_2 40 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 215 272 (accept_3_2 37 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 215 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 215 272 (Polychromatic418967fa.accept_21_14_5_20_1_12299 35 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 272 (accept_3_2 34 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 215 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 215 272 (accept_3_2 31 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 215 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 215 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 272 (accept_3_2 28 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 215 272 (accept_3_2 25 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 215 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 215 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 272 (accept_3_2 22 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 215 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 272
  (Polychromatic418967fa.accept_23_20_8_19_1_10295 20 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 215 272 (accept_3_2 19 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 215 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 215
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 272 (accept_3_2 16 215
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 215 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 272 (accept_3_2 13 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 215 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 272 (Polychromatic418967fa.accept_7_4_5_6_1_344
  11 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 272 (accept_3_2 10
  215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 215 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 272 (accept_3_2 7 215 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 215 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 215 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 272 (accept_3_2 4 215
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 272 (accept_3_2 1 215 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 214 272 (Eq.refl Bool.true) (allA_of_3_0
  59 214 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 213 272 (Eq.refl Bool.true) (allA_succ_of_accept 59
  213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 213 272 (accept_3_2 58 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 213 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 213 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 213 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 213
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 272 (accept_3_2 55 213
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 272
  (Polychromatic418967fa.accept_12_6_9_8_1_165 54 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 213 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 213 272 (accept_3_2 52 213 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 213 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 272 (Polychromatic418967fa.accept_9_5_6_2_1_161
  50 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 272 (accept_3_2 49
  213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 48 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 213 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 272 (accept_3_2 46 213 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 213 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 213 272 (accept_3_2 43 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 213 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 272 (accept_3_2 40 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 213 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 272
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 272 (accept_3_2 37 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 213 272 (Polychromatic418967fa.accept_19_17_4_6_1_5810 36 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 272 (accept_3_2 34 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 213 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 213 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 272 (accept_3_2 31 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 213 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 272 (accept_3_2 28 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 213 272 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 272 (accept_3_2 25 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 213 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 272 (accept_3_2 22 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 213 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 272
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 272 (accept_3_2 19 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 272 (accept_3_2 16 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 272 (accept_3_2 13 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 272 (accept_3_2 10 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 272 (accept_3_2 7 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 272 (accept_3_2 4 213 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 213 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 272 (accept_3_2 1 213 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 212 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 212 272 4 15 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 212 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 212 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 212 272 2 29 106 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 212 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 212 272 4 14 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 212 272 (accept_3_2 55 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 212 272 2 27 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 212 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 212 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 212 272 4 13 53 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 212 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 212 272 2 25 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 212 272 (accept_3_2 49 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 212 272 4 12 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 212 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 212 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 272 2 23 106 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 272 4 11 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 272 (accept_3_2 43 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 272 2 21 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 41 212 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 272 4 10 53 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 272 2 19 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 272 (accept_3_2 37 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 272 4 9 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 212 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 212 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 272 2 17 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 212 272 4 8 53 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 212 272 (accept_3_2 31
  212 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 212 272 2 15 106 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 212 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 212 272 4 7 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 212 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 212 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 212 272 2 13 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 212 272 (accept_3_2 25 212 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 212 272 4 6 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 272 (Polychromatic418967fa.accept_19_4_3_6_1_11389 23 212
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 272 2 11 106 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 272 4 5 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 212 272 (accept_3_2 19 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  212 272 2 9 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 212 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 212 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 272 4 4 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 212 272 2 7 106 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 212 272 (accept_3_2 13
  212 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 212 272 4 3 53 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 212 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 212 272 2 5 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 212 272 (Polychromatic418967fa.accept_19_9_3_6_1_11390 9 212 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 212 272 4 2 53 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 212 272 (accept_3_2 7 212 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212 272 2 3 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 212 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 272 4 1 53 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 272 2 1 106 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 272 (accept_3_2 1 212 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 211 272 (Eq.refl Bool.true)
  (allA_of_3_0 62 211 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 210 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 210 272 2 31 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 210 272 (accept_3_2 61 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 210 272 2 30 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 210 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 210 272 2 29 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 210 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 210 272 2 28 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 210 272 (accept_3_2 55 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 272 2 27 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 210 272 2 26 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 210 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 210 272 2 25 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 210 272 (accept_3_2 49 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 272 2 24 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 272 (Polychromatic418967fa.accept_24_23_18_8_1_4564 47 210 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 272 2 23 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 210 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 210 272 2 22 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 210 272 (accept_3_2 43 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 272 2 21 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 210 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 272 2 20 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 210 272 2 19 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 210 272 (accept_3_2 37 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 272 2 18 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 272 2 17 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 272 2 16 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 272 (accept_3_2 31 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 272 2 15 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 272 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 210 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 272 2 14 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 210 272 2 13 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 210 272 (accept_3_2 25 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 272 2 12 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 272 2 11 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 272 2 10 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 272 (accept_3_2 19 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 272 2 9 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 272 2 8 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 272 2 7 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 272 (accept_3_2 13 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 272 2 6 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 272 (Polychromatic418967fa.accept_19_11_1_6_1_5752 11 210 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 272 2 5 105 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 272 2 4 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 272 (accept_3_2 7 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 272 2 3 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 210 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 272 2 2 105 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 272 2 1 105 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 272 (accept_3_2 1 210 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 209 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 209 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 272 (accept_3_2 61 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 60 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 209 272 (Polychromatic418967fa.accept_20_19_9_12_1_9740 59 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 209 272 (accept_3_2 58 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 209 272
  (Polychromatic418967fa.accept_22_12_11_8_1_8964 56 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 209 272 (accept_3_2 55 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 209 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 209 272 (accept_3_2 52 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 209 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 209 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 272 (accept_3_2 49 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 209 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 48 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 272 (accept_3_2 46 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 272 (accept_3_2 43 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 272 (Polychromatic418967fa.accept_15_12_14_2_1_3794 42 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 272 (accept_3_2 40 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 272 (accept_3_2 37 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 272 (Polychromatic418967fa.accept_22_14_11_8_1_7212 36 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 272
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 35 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 272 (accept_3_2 34 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 272 (Polychromatic418967fa.accept_18_14_11_2_1_5068 32 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 272 (accept_3_2 31 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 272 (Polychromatic418967fa.accept_24_6_17_8_1_15024 30 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 272
  (Polychromatic418967fa.accept_23_6_2_19_1_16706 29 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 209 272 (accept_3_2 28 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 272 (accept_3_2 25 209
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 272
  (Polychromatic418967fa.accept_13_11_1_12_1_742 24 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 209 272 (Polychromatic418967fa.accept_20_3_9_12_1_6671 23 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 272 (accept_3_2 22 209 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 20 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 272 (accept_3_2 19 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 272 (accept_3_2 16 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 209 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 272 (accept_3_2 13 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 272 (accept_3_2 10 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 272 (accept_3_2 7 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 272 (Polychromatic418967fa.accept_23_6_2_19_1_16706 6 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 272 (accept_3_2 4 209 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 272 (accept_3_2 1 209 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 208 272 (Eq.refl Bool.true)
  (allA_of_3_0 65 208 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 207 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 207 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 207 272 (accept_3_2 64 207 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 207 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 207 272
  (Polychromatic418967fa.accept_20_2_7_12_1_5215 62 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 207 272 (accept_3_2 61 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 207 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 272 (accept_3_2 58 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 207 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 57 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 272
  (Polychromatic418967fa.accept_19_18_17_6_1_5775 56 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 207 272 (accept_3_2 55 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 207 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 207 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 207 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 272 (accept_3_2 52 207 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 272 (Polychromatic418967fa.accept_7_2_4_6_1_166
  51 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 272
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 207 272 (accept_3_2 49 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 207 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 272 (accept_3_2 46 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 207 272 (accept_3_2 43 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 207 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 272 (accept_3_2 40 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 272 (accept_3_2 37 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 207 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 272 (accept_3_2 34 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 272 (accept_3_2 31 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 207 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 272 (accept_3_2 28 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 272 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 207 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 272 (accept_3_2 25 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 272 (accept_3_2 22 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 207 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 272
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 20 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 272 (accept_3_2 19 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 272 (accept_3_2 16 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 272 (accept_3_2 13 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 272 (accept_3_2 10 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 272
  (Polychromatic418967fa.accept_19_8_17_6_1_5728 8 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 272 (accept_3_2 7 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 272 (accept_3_2 4 207 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 272 (accept_3_2 1 207 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 206 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 206 272 2 33 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 206 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 206 272 2 32 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 206 272
  (Polychromatic418967fa.accept_25_13_6_22_1_11466 63 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 206 272 2 31 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 206 272 (accept_3_2 61 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 206 272 2 30 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 206 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 206 272 2 29 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 206 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 206 272 2 28 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 206 272 (accept_3_2 55 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 206 272 2 27 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 206 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 206 272 2 26 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 206 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 206 272 2 25 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 206 272 (accept_3_2 49 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 206 272 2 24 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 206 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 206 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 272 2 23 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 272
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 272 2 22 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 272 (accept_3_2 43 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 272 2 21 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 272 2 20 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 272 2 19 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 272 (accept_3_2 37 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 272 2 18 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 206 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 272 2 17 103 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 272 2 16 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 272 (accept_3_2 31 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 272 2 15 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 272 2 14 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 272
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 206 272 2 13 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 206 272 (accept_3_2 25 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 272 2 12 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 272 2 11 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 272 2 10 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 272 (accept_3_2 19 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 272 2 9 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 272 2 8 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 272 2 7 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 272 (accept_3_2 13 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 272 2 6 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 272 2 5 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 272 2 4 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 272 (accept_3_2 7 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 272 2 3 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 206 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 272 2 2 103 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 272 2 1 103 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 272 (accept_3_2 1 206 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 205 272 (Eq.refl Bool.true)
  (allA_of_3_0 68 205 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 204 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 204 272 68 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 204 272 (accept_3_2 67 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66
  204 272 2 33 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 204 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 204 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 204 272 4 16 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 204 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164
  63 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 204 272 2 31 102 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 272
  (accept_3_2 61 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 204 272 4 15 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 204 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 204 272 2 29 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 204 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 204 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 204 272 4 14 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 272 (accept_3_2 55 204 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 204 272 2 27 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 204 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53
  204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 272 4 13 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 204 272 17 3 12 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 204 272 2 25 102
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 272
  (accept_3_2 49 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 204 272 4 12 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 204 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 272 2 23 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 204 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 45 204 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 204 272 4 11 51 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 272 (accept_3_2 43 204 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 204 272 2 21 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 204 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 204 272 4 10 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 204 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 204 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 204 272 2 19 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 272 (accept_3_2 37 204 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 272 4 9 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 272 34 1 6 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 204 272 4 8 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 204 272 (accept_3_2 31 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  204 272 2 15 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 204 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 204 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 272 4 7 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 272 (Polychromatic418967fa.accept_10_7_4_2_1_903
  27 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 272 2 13 102 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 272
  (accept_3_2 25 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 272 4 6 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 204 272 2 11 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 204 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 204 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 204 272 4 5 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 272 (accept_3_2 19 204 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 272 2 9 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 204 272 17 1 12 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 204 272 4 4 51 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 272
  (Polychromatic418967fa.accept_22_15_6_8_1_13639 15 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 204 272 2 7 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 204 272 (accept_3_2 13 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 272 4 3 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 272 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 204 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 272 2 5 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 204 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 272 4 2 51 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 272 (accept_3_2 7
  204 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 272 2 3 102 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 204 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 272 4 1 51 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 204 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 204 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 272 2 1 102 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 272 (accept_3_2 1 204 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 203 272 (Eq.refl Bool.true) (allA_succ_of_accept 69 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12
  69 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 203 272
  (Polychromatic418967fa.accept_11_2_5_8_1_470 68 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 203 272 (accept_3_2 67 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 203 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 203 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 65 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 272 (accept_3_2 64 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 203 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 203 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 203 272 (accept_3_2 61 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 203 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 203 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 59 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 272 (accept_3_2 58 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 203 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 203 272
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 203 272 (accept_3_2 55 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 272 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 203 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 272 (accept_3_2 52 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 203 272 (accept_3_2 49 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 203 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 47 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 272 (accept_3_2 46 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 203 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 272 (accept_3_2 43 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 272 (accept_3_2 40 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 272 (accept_3_2 37 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 272 (accept_3_2 34 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 203 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 272
  (Polychromatic418967fa.accept_21_11_14_20_1_12235 32 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 203 272 (accept_3_2 31 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 203 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 272 (Polychromatic418967fa.accept_14_1_7_6_1_3604 29 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 272 (accept_3_2 28 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 203 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 272 (accept_3_2 25 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 203 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 272
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 203 272 (accept_3_2 22 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 272 (accept_3_2 19 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 272
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 203 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 272 (accept_3_2 16 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 272 (Polychromatic418967fa.accept_11_3_5_8_1_458
  14 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 272 (accept_3_2 13
  203 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 203 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 272 (accept_3_2 10 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 272 (accept_3_2 7 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 203 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 272 (accept_3_2 4 203 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 203 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 2
  203 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 272 (accept_3_2 1 203
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 202 272 (Eq.refl Bool.true)
  (allA_of_3_0 71 202 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 201 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 201 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 272 (accept_3_2 70 201 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 272 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 201 272 (accept_3_2 67
  201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 201 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 201 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 272 (accept_3_2 64 201 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 201 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 201 272 (accept_3_2 61 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 201 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 272 (accept_3_2 58 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 201 272 (accept_3_2 55 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 201 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 272 (accept_3_2 52 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 272 (accept_3_2 49 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 272 (accept_3_2 46 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 45 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 272 (accept_3_2 43 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 272 (accept_3_2 40 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 272 (accept_3_2 37 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 272 (accept_3_2 34 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 272 (accept_3_2 31 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 272 (accept_3_2 28 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 272 (accept_3_2 25 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 272 (accept_3_2 22 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 272 (Polychromatic418967fa.accept_23_21_17_19_1_10313 21 201 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 272
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 272 (accept_3_2 19 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 272 (accept_3_2 16 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 272 (accept_3_2 13 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 272 (accept_3_2 10 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 272 (accept_3_2 7 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 272 (accept_3_2 4 201 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 201 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 272
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 272 (accept_3_2 1 201 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 200 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 200 272 8 9 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 200 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 200 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 200 272 2 35 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 200 272 (Polychromatic418967fa.accept_13_4_5_12_1_751
  69 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 200 272 4 17 50 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 200 272
  (accept_3_2 67 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 200 272 2 33 100 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 200 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 200 272 8 8 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 200 272 (Polychromatic418967fa.accept_15_3_5_2_1_2816 63 200 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 200 272 2 31 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 200 272 (accept_3_2 61 200 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 200 272 4 15 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 200 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 200 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 200 272 2 29 100 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 200 272
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 57 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 200 272 8 7 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 200 272 (accept_3_2 55 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  200 272 2 27 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 200 272 (Polychromatic418967fa.accept_13_1_5_12_1_306 53 200 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 272 4 13 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 51
  200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 200 272 2 25 100 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 200 272
  (accept_3_2 49 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 200 272 8 6 25 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 200 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 200 272 2 23 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 200 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 200 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 200 272 4 11 50 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 200 272 (accept_3_2 43 200 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 200 272 2 21 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 200 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043
  41 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 272 8 5 25 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 272
  (Polychromatic418967fa.accept_19_1_10_6_1_5726 39 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 200 272 2 19 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 272 (accept_3_2 37 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 200 272 4 9 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 200 272 (Polychromatic418967fa.accept_19_16_10_6_1_11403 35 200 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 200 272 2 17 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 200 272 8 4 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 200 272 (accept_3_2 31 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  200 272 2 15 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 200 272 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 200 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 272 4 7 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 272 (Polychromatic418967fa.accept_11_5_2_8_1_866
  27 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 272 2 13 100 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 200 272
  (accept_3_2 25 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 200 272 8 3 25 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 200 272 2 11 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 200 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 200 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 200 272 4 5 50 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 200 272 (accept_3_2 19 200 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 200 272 2 9 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 200 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 200 272 8 2 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 200 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 200 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 272 2 7 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 272 (accept_3_2 13 200 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 272 4 3 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 200
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 272 2 5 100 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 272 8 1 25 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 272 (accept_3_2 7 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200
  272 2 3 100 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  200 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 200 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 200 272 4 1 50 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 200 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 272 2 1 100 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 272 (accept_3_2 1 200 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 199 272 (Eq.refl
  Bool.true) (allA_of_3_0 74 199 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 198 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 198 272 2 37 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 198 272 (accept_3_2 73 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 198 272 2 36 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 198 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 272 2 35 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 198 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 198 272 2 34 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 198 272 (accept_3_2 67 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 272 2 33 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 198 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 272 2 32 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 198 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 198 272 2 31 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 198 272 (accept_3_2 61 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 272 2 30 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 272 2 29 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 198 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 198 272 2 28 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 198 272 (accept_3_2 55 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 272 2 27 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 272 2 26 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 272 2 25 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 272 (accept_3_2 49 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 272 2 24 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 198 272 (Polychromatic418967fa.accept_27_20_9_2_1_16705 47 198 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 272 2 23 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 272 2 22 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 272 (accept_3_2 43 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 272 2 21 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 272 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 198 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 272 2 20 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 272 2 19 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 272 (accept_3_2 37 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 272 2 18 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 272 2 17 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 272 2 16 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 272 (accept_3_2 31 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 272 2 15 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 272 2 14 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 272 2 13 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 272 (accept_3_2 25 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 272 2 12 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 272 (Polychromatic418967fa.accept_21_2_9_20_1_9260 23 198 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 272 2 11 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 272 2 10 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 272 (accept_3_2 19 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 272 2 9 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 272 2 8 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 272 2 7 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 272 (accept_3_2 13 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 272 2 6 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 198 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 272 2 5 99 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 272 2 4 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 272 (accept_3_2 7 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  272 2 3 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 198 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 272 2 2 99 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 198 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 272 2 1 99 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 272 (accept_3_2 1 198 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 197 272 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 197 272 (Polychromatic418967fa.accept_10_4_7_2_1_211
  74 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 197 272 (accept_3_2 73
  197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 197 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 197 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 71 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 272 (accept_3_2 70 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 197 272 (Polychromatic418967fa.accept_7_5_1_6_1_163
  68 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 272 (accept_3_2 67
  197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 197 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 197 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 197 272 (accept_3_2 64 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 272 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 272 (accept_3_2 61
  197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 197 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 272 (accept_3_2 58 197 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 272
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 56 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 272 (accept_3_2 55 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 272 (accept_3_2 52 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 197 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 272 (accept_3_2 49 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 272 (accept_3_2 46 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 272 (accept_3_2 43 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 272 (accept_3_2 40 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 272 (accept_3_2 37 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 272 (accept_3_2 34 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 272 (accept_3_2 31 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 272 (accept_3_2 28 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 197 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 272 (accept_3_2 25 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 272 (accept_3_2 22 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 272 (accept_3_2 19 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 272 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 272 (accept_3_2 16 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 272 (accept_3_2 13 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 272 (accept_3_2 10 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 272
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 8 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 272 (accept_3_2 7 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 272 (accept_3_2 4 197 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 197 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 272 (accept_3_2 1 197 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 196 272 (Eq.refl
  Bool.true) (allA_of_3_0 77 196 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 195 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 195 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 195 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 272 (accept_3_2 76 195 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 195 272
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 74 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 195 272 (accept_3_2 73 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 195 272 (Polychromatic418967fa.accept_19_15_5_6_1_5760 72 195 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 195 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 272 (accept_3_2 70 195 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 272
  (Polychromatic418967fa.accept_25_19_20_22_1_16704 69 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 195 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 272 (accept_3_2 67 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 195 272 (accept_3_2 64 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 195 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 272 (accept_3_2 61 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 272 (Polychromatic418967fa.accept_19_3_5_6_1_7135 60 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 272 (accept_3_2 58 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 272 (Polychromatic418967fa.accept_19_18_5_6_1_2004 56 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 272 (accept_3_2 55 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 195
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 272 (accept_3_2 52 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 195 272 (Polychromatic418967fa.accept_21_9_6_20_1_1903 51 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 195 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 272 (accept_3_2 49 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 272 (accept_3_2 46 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 195 272 (Polychromatic418967fa.accept_19_7_5_6_1_9961 45 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 195 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 272 (accept_3_2 43 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 272 (accept_3_2 40 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 272 (accept_3_2 37 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 272 (Polychromatic418967fa.accept_21_15_6_20_1_12272 36
  195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 272 (accept_3_2 34 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 272 (accept_3_2 31 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 272 (accept_3_2 28 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 272 (accept_3_2 25 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 272 (Polychromatic418967fa.accept_21_3_6_20_1_9278 24 195 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 272 (accept_3_2 22 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 272 (Polychromatic418967fa.accept_19_1_5_6_1_5811 20 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 272 (accept_3_2 19 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 195
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 272 (accept_3_2 16 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 272 (Polychromatic418967fa.accept_19_15_5_6_1_5760 15 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 272 (accept_3_2 13 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 272 (accept_3_2 10 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 272 (Polychromatic418967fa.accept_21_9_6_20_1_1903 9 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 272 (accept_3_2 7 195 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 272 (accept_3_2 4 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 272 (Polychromatic418967fa.accept_21_2_6_20_1_6059 2 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 272 (accept_3_2 1 195 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 194 272 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 194 272 2 39 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 194 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 194 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 194 272 2 38 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 194 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 194 272 2 37 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 194 272 (accept_3_2 73 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 194 272 2 36 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 194 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 194 272 2 35 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 194 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 194 272 2 34 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 194 272 (accept_3_2 67 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 194 272 2 33 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 194 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 272 2 32 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 272
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 194 272 2 31 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 194 272 (accept_3_2 61 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 272 2 30 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 194 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 272 2 29 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 272 2 28 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 272 (accept_3_2 55 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 272 2 27 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 272 2 26 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 272 2 25 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 272 (accept_3_2 49 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 272 2 24 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 272 2 23 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 272
  (Polychromatic418967fa.accept_22_1_18_8_1_5619 45 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 194 272 2 22 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 194 272 (accept_3_2 43 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 272 2 21 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 272 2 20 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 272 2 19 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 272 (accept_3_2 37 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 272 2 18 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 272 2 17 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 194 272 2 16 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 194 272 (accept_3_2 31 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 272 2 15 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 272 2 14 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 272 2 13 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 272 (accept_3_2 25 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 272 2 12 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 194 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 272 2 11 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 272 2 10 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 272 (accept_3_2 19 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 272 2 9 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 272 2 8 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 272 2 7 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 272 (accept_3_2 13 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 272 2 6 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 194 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 272 2 5 97 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 272
  (Polychromatic418967fa.accept_22_9_18_8_1_8979 9 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 272 2 4 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 272 (accept_3_2 7 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  272 2 3 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 194 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 272 2 2 97 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 194 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 272 2 1 97 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 272 (accept_3_2 1 194 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 193 272 (Eq.refl
  Bool.true) (allA_of_3_0 80 193 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 192 272 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 192 272 16 5 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 192 272 (accept_3_2 79 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 272 2 39 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 192 272 4 19 48 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 192 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 75 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 192 272 2 37 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 192 272 (accept_3_2 73 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 272 8 9 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 192 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 192 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 192 272 2 35 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 192 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 192 272 4 17 48 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 192 272 (accept_3_2 67
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 192 272 2 33 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 192 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 192 272 16 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 192 272 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 192 272 2 31 96 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 192 272 (accept_3_2 61 192 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 192 272 4 15 48 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 192 272 2 29 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 192 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 57 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 192 272 8 7 24 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 192 272 (accept_3_2 55 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 192 272 2 27 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 192 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 272 4 13 48 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 192 272 2 25 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 272 (accept_3_2 49 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 272 16 3 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 47 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 272 2 23 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 192 272 4 11 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 192 272 (accept_3_2 43 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 272 2 21 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 272 8 5 24 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 272 2 19 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 272 (accept_3_2 37 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 272 4 9 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 192 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 272 2 17 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 272 16 2 12 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 272 (accept_3_2 31
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 272 2 15 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 272
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 192 272 4 7 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 192 272 (Polychromatic418967fa.accept_19_8_2_6_1_8677 27 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 272 2 13 96 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 272 (accept_3_2 25 192 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 272 8 3 24 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 192 272 2 11 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 192 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 272 4 5 48 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 272 (accept_3_2 19 192 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 272 2 9 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 272 16 1 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 192 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 272 2 7 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 272 (accept_3_2 13 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 272 4 3 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 272 2 5 96 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 272 8 1 24 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 272 (accept_3_2 7 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  272 2 3 96 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 192 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 272 4 1 48 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 192 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 192 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 272 2 1 96 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 272 (accept_3_2 1 192 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 191 272 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 191 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 80
  191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 191 272 (accept_3_2 79
  191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 191 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 191 272 (Polychromatic418967fa.accept_21_14_2_20_1_12297 77 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 191 272 (accept_3_2 76 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 191 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 191 272 (accept_3_2 73 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 191 272 (Polychromatic418967fa.accept_21_9_2_20_1_857 72 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 191 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 191 272 (accept_3_2 70 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 191 272
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 68 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 191 272 (accept_3_2 67 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 191 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 191 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 191 272 (accept_3_2 64 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 191 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 62 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 191 272 (accept_3_2 61 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 191 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 272 (accept_3_2 58 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 191 272 (accept_3_2 55 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 191 272 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 191 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 272 (accept_3_2 52 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 272 (accept_3_2 49 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 272 (Polychromatic418967fa.accept_19_10_1_6_1_5755 48 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 272 (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 272 (accept_3_2 46 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 191 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 272
  (Polychromatic418967fa.accept_23_21_7_19_1_10347 44 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 191 272 (accept_3_2 43 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 191 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 191 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 272 (Polychromatic418967fa.accept_19_3_1_6_1_3114 41 191
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 272 (accept_3_2 40 191
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 191 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 191 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 272 (accept_3_2 37 191 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 191 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 272
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 272 (accept_3_2 34 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 272 (accept_3_2 31 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 272 (Polychromatic418967fa.accept_19_11_1_6_1_5752 30 191 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 272 (accept_3_2 28 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 272 (accept_3_2 25 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 191 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 272 (accept_3_2 22 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 272 (accept_3_2 19 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 191 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 272 (accept_3_2 16 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 272 (accept_3_2 13 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 191
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 272 (accept_3_2 10 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 272 (accept_3_2 7 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 191 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 272
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 272 (accept_3_2 4 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 272 (accept_3_2 1 191 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 190 272 (Eq.refl
  Bool.true) (allA_of_3_0 83 190 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 189 272 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 189 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 189 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 272 (accept_3_2 82 189 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 189 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 189 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 272
  (Polychromatic418967fa.accept_25_5_14_22_1_14937 80 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 189 272 (accept_3_2 79 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 189 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 189 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 272 (accept_3_2 76 189 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 272
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 75 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 189 272 (Polychromatic418967fa.accept_19_17_18_6_1_7192 74 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 189 272 (accept_3_2 73 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 189 272 (Polychromatic418967fa.accept_26_20_7_12_1_14805 72
  189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 189 272 (accept_3_2 70 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 189 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 69 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 189 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 68 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 272 (accept_3_2 67 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 189 272 (accept_3_2 64 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 189 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 189 272 (Polychromatic418967fa.accept_13_10_7_12_1_2782 62 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 272 (accept_3_2 61 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 189 272 (accept_3_2 58 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 189 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 189 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 272 (accept_3_2 55 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 189 272 (accept_3_2 52 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 189 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 50 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 272 (accept_3_2 49 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 272 (Polychromatic418967fa.accept_25_23_14_22_1_16703 48
  189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 272 (accept_3_2 46 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 272 (accept_3_2 43 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 272 (accept_3_2 40 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 38 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 272 (accept_3_2 37 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 272 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 272 (accept_3_2 34 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 272 (Polychromatic418967fa.accept_22_11_13_8_1_7242 33 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 272 (accept_3_2 31 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 272 (accept_3_2 28 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 272 (Polychromatic418967fa.accept_15_11_9_2_1_4780 26 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 272 (accept_3_2 25 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 272 (accept_3_2 22 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 272 (Polychromatic418967fa.accept_19_1_18_6_1_3110 20 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 272 (accept_3_2 19 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 189
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 272 (accept_3_2 16 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 272 (Polychromatic418967fa.accept_14_1_7_6_1_3604 15 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 272 (Polychromatic418967fa.accept_23_14_5_19_1_11850 14 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 272 (accept_3_2 13 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 272 (Polychromatic418967fa.accept_19_12_18_6_1_14021 12
  189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 272 (accept_3_2 10 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 272 (Polychromatic418967fa.accept_19_9_18_6_1_5778 9 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 272 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 272 (accept_3_2 7 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 189 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 272 (accept_3_2 4 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 189 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 272 (Polychromatic418967fa.accept_20_2_9_12_1_2546 2 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 272 (accept_3_2 1 189 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 188 272
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 188 272 4 21 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 188 272 (Polychromatic418967fa.accept_13_5_6_12_1_2750 83 188
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 188 272 2 41 94 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 188 272
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 188 272 4 20 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 188 272 (accept_3_2 79 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 188 272 2 39 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 188 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 188 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 188 272 4 19 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 188 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 188 272 2 37 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 188 272 (accept_3_2 73 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 188 272 4 18 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 188 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 71 188 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 272 2 35 94 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 272 4 17 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 272 (accept_3_2 67 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 272 2 33 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 188 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 272 4 16 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 272
  (Polychromatic418967fa.accept_24_15_20_8_1_13325 63 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 188 272 2 31 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 188 272 (accept_3_2 61 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 272 4 15 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 188 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 272 2 29 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 272 4 14 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 272 (accept_3_2 55 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 272 2 27 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 53 188 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 272 4 13 47 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 272 2 25 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 272 (accept_3_2 49 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 272 4 12 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 272 (Polychromatic418967fa.accept_19_9_17_6_1_3108 47 188 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 272 2 23 94 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 188 272 4 11 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 188 272 (accept_3_2 43 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 272 2 21 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 188 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 272 4 10 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 272 2 19 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 272 (accept_3_2 37 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 272 4 9 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 188 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 272 2 17 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 272 4 8 47 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 272 (accept_3_2 31
  188 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 272 2 15 94 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 272
  (Polychromatic418967fa.accept_22_7_12_8_1_4002 29 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 188 272 4 7 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 188 272 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 188 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 272 2 13 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 272 (accept_3_2 25 188 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 272 4 6 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 188 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 272 2 11 94 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 272 4 5 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 188 272 (accept_3_2 19 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  188 272 2 9 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 188 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 188 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 272 4 4 47 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 272 2 7 94 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 272 (accept_3_2 13
  188 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 272 4 3 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 272
  (Polychromatic418967fa.accept_19_11_17_6_1_7157 11 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 188 272 2 5 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 188 272 (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 188 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 272 4 2 47 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 272 (accept_3_2 7 188 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 272 2 3 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5
  188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 272 4 1 47 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 272 2 1 94 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 272 (accept_3_2 1 188 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_272_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


