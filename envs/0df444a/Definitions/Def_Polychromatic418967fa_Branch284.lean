-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch284
-- name    : Polychromatic418967fa_Branch284
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:35:27.903591+00:00
-- url     : https://prove2.me/theorems/567642a4-30f3-4c53-9670-2ef5f9590237
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch284_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_284 : allB 284 284 :=
  allB_succ' 2 283 284 (Eq.refl Bool.true) (allA_of_3_0 2 283 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  282 284 (Eq.refl Bool.true) (allA_succ_of_gcd 2 282 284 2 1 141 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 282 284 (accept_3_2 1 282 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 282 284))) (allB_succ' 4 281 284 (Eq.refl Bool.true) (allA_succ_of_accept 3 281 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 281 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 281 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 281 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 281 284 (accept_3_2 1 281 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 281 284)))) (allB_succ' 5 280 284 (Eq.refl Bool.true) (allA_of_3_0 5 280 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 279 284 (Eq.refl Bool.true) (allA_succ_of_accept 5 279 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 279 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 279 284 (accept_3_2 4 279 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  279 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 279 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 279 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 279 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 279 284 (accept_3_2 1 279 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 279 284)))))) (allB_succ' 7 278 284 (Eq.refl Bool.true) (allA_succ_of_gcd 6 278 284 2 3
  139 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 278 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 5 278 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 278 284 2 2 139 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 278 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 278 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 278 284 2 1 139 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 278 284 (accept_3_2 1 278 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 278 284))))))) (allB_succ' 8 277 284 (Eq.refl Bool.true) (allA_of_3_0 8 277
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 276 284 (Eq.refl Bool.true) (allA_succ_of_gcd 8 276 284 4 2
  69 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 276 284
  (accept_3_2 7 276 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 276 284 2 3 138 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 276 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 276 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 276 284 4 1 69 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 276 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 276 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 276 284 2 1 138 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 284 (accept_3_2 1 276 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 276 284))))))))) (allB_succ' 10 275 284 (Eq.refl Bool.true) (allA_succ_of_accept 9 275
  284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 275 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 275 284 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 275 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 275 284 (accept_3_2 7 275 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 275 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 275 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 275 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  275 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 275 284 (accept_3_2 4 275
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 275 284 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 275 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 275 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 275 284 (accept_3_2 1 275 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275
  284)))))))))) (allB_succ' 11 274 284 (Eq.refl Bool.true) (allA_of_3_0 11 274 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 273 284 (Eq.refl Bool.true) (allA_succ_of_accept 11 273 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 273 284 (accept_3_2 10 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  273 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 273 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 273 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 284 (accept_3_2 7 273 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 273 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 273 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 273 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 273 284 (accept_3_2 4 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  273 284 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 273 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 273 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 273 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 284 (accept_3_2 1 273 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 273 284)))))))))))) (allB_succ' 13 272 284 (Eq.refl Bool.true) (allA_succ_of_gcd 12 272
  284 4 3 68 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  272 284 (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 272 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 272 284 2 5 136 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 272 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 272 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 272 284 4 2 68 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 272 284 (accept_3_2 7 272 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 272 284 2 3 136 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 272 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5
  272 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 272 284 4 1 68 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 272 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 272 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 272 284 2 1 136 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 272 284 (accept_3_2 1 272 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 272
  284))))))))))))) (allB_succ' 14 271 284 (Eq.refl Bool.true) (allA_of_3_0 14 271 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 270 284 (Eq.refl Bool.true) (allA_succ_of_gcd 14 270 284 2 7 135 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 270 284 (accept_3_2 13 270 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 270 284 2 6 135 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 270 284
  (Polychromatic418967fa.accept_19_11_4_18_1_5226 11 270 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 270 284 2 5 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 270 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 270 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 270 284 2 4 135 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 270 284 (accept_3_2 7 270 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 270 284 2 3 135 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 270 284
  (Polychromatic418967fa.accept_19_5_4_18_1_5242 5 270 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 270 284 2 2 135 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 270 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 270 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 270 284 2 1 135 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 284 (accept_3_2 1 270 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 270 284))))))))))))))) (allB_succ' 16 269 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 269 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 269 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 269 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 269
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 269 284 (accept_3_2 13 269
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 269 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 269 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 269 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 269 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 269 284 (accept_3_2 10 269 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 269 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 269 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 269 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8
  269 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 269 284 (accept_3_2 7 269
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 269 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 269 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 269 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 269 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 284 (accept_3_2 4 269 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 269 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 269 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 269 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  269 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 269 284 (accept_3_2 1 269
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 269 284)))))))))))))))) (allB_succ' 17 268 284 (Eq.refl
  Bool.true) (allA_of_3_0 17 268 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 267 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 267 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 267 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 267 284 (accept_3_2 16 267 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 267 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 267 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 267 284 (Polychromatic418967fa.accept_13_1_7_11_1_702
  14 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 267 284 (accept_3_2 13
  267 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 267 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 267 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 267 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 284 (accept_3_2 10 267 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 267 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 267 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 267 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 267 284 (accept_3_2 7 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  267 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 267 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 267 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 284 (accept_3_2 4 267 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 267 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 267 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 267 284 (accept_3_2 1 267 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267
  284)))))))))))))))))) (allB_succ' 19 266 284 (Eq.refl Bool.true) (allA_succ_of_gcd 18 266 284 2 9 133 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 266 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 17 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 266 284 2 8 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 266 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 266 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 266 284 2 7 133 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 266 284 (accept_3_2 13 266 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 266 284 2 6 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 266 284 (Polychromatic418967fa.accept_12_11_2_8_1_511
  11 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 266 284 2 5 133 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 266 284
  (Polychromatic418967fa.accept_27_9_23_14_1_2233 9 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 266 284 2 4 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 266 284 (accept_3_2 7 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 266 284 2 3 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 266 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 266 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 266 284 2 2 133 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 266 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 266 284 2 1 133 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 266 284 (accept_3_2 1 266 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266
  284))))))))))))))))))) (allB_succ' 20 265 284 (Eq.refl Bool.true) (allA_of_3_0 20 265 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 264 284 (Eq.refl Bool.true) (allA_succ_of_gcd 20 264 284 4 5 66 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 264 284 (accept_3_2 19 264 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 264 284 2 9 132 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 264 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 264 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 264 284 4 4 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 264 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 264 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 264 284 2 7 132 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 264 284 (accept_3_2 13 264 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 264 284 4 3 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 264 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 264 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 264 284 2 5 132 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 264 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 264 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 264 284 4 2 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 264 284 (accept_3_2 7 264 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264
  284 2 3 132 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  264 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 264 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 264 284 4 1 66 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 264 284 (Polychromatic418967fa.accept_16_3_8_12_1_2736 3 264 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 264 284 2 1 132 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 284 (accept_3_2 1 264 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 264 284))))))))))))))))))))) (allB_succ' 22 263 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 263 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 263 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 20 263
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 263 284 (accept_3_2 19 263
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 263 284
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 263 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 263 284 (accept_3_2 16 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 263 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 263 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 263 284 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 284 (accept_3_2 13
  263 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 263 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 263 284 (accept_3_2 10 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 263 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 263 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 263 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 284 (accept_3_2 7 263
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 6 263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 263 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 263 284 (accept_3_2 4 263 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 263 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 263 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 263 284 (Polychromatic418967fa.accept_12_2_11_8_1_504
  2 263 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 284 (accept_3_2 1
  263 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 263 284)))))))))))))))))))))) (allB_succ' 23 262 284
  (Eq.refl Bool.true) (allA_of_3_0 23 262 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 261 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 261 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 261 284 (accept_3_2 22 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 261 284 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 261 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 261 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 261 284 (accept_3_2 19 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 261 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 261 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 261 284 (accept_3_2 16 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 261 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 261 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 261 284
  (Polychromatic418967fa.accept_25_14_11_9_1_17396 14 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 261 284 (accept_3_2 13 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 261 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 261 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 261 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 261 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 261 284 (accept_3_2 10 261 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 261 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 261 284
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 8 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 261 284 (accept_3_2 7 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  261 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 261 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 284 (accept_3_2 4 261 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 261 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 261 284
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 261 284 (accept_3_2 1 261 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261
  284)))))))))))))))))))))))) (allB_succ' 25 260 284 (Eq.refl Bool.true) (allA_succ_of_gcd 24 260 284 4 6 65 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 260 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 260 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 260 284 2 11 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 260 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 260 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 260 284 4 5 65 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 260 284 (accept_3_2 19 260 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 260 284 2 9 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 260 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  260 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 260 284 4 4 65 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 260 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 260 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 260 284 2 7 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 260 284 (accept_3_2 13 260 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 260 284 4 3 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 260 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 260 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 260 284 2 5 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 260 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 9
  260 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 260 284 4 2 65 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 260 284 (accept_3_2 7
  260 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 260 284 2 3 130 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 260 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 260 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 260 284 4 1 65 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 260 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 260 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 260 284 2 1 130 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 260 284 (accept_3_2 1 260 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 260 284))))))))))))))))))))))))) (allB_succ' 26 259 284 (Eq.refl Bool.true)
  (allA_of_3_0 26 259 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 258 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 258 284 2 13 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 258 284 (accept_3_2 25 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 258 284 2 12 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 258 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 258 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 258 284 2 11 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 258 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 258 284 2 10 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 258 284 (accept_3_2 19 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 258 284 2 9 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 258 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 258 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 258 284 2 8 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 258 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 258 284 2 7 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 258 284 (accept_3_2 13 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 258 284 2 6 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 258 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 258 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 258 284 2 5 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 258 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 258 284 2 4 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 258 284 (accept_3_2 7 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 284 2 3 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 258 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 258 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 258 284 2 2 129 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 258 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 258 284 2 1 129 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 258 284 (accept_3_2 1 258 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258
  284))))))))))))))))))))))))))) (allB_succ' 28 257 284 (Eq.refl Bool.true) (allA_succ_of_accept 27 257 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 257 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 257 284 (accept_3_2 25 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 257 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 257 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 257 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 257 284 (accept_3_2 22 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 257 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 257 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 257 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 257 284 (accept_3_2 19 257 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 257 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 257 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 284
  (Polychromatic418967fa.accept_13_4_10_11_1_1908 17 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 257 284 (accept_3_2 16 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 257 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 257 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 257
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 284 (accept_3_2 13 257
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 257 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 257 284 (accept_3_2 10 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 257 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 257 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 257 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 284 (accept_3_2 7 257
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 257 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 257 284 (accept_3_2 4 257 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 257 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 257 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 257 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  257 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 284 (accept_3_2 1 257
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 257 284)))))))))))))))))))))))))))) (allB_succ' 29 256 284
  (Eq.refl Bool.true) (allA_of_3_0 29 256 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 255 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 255 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 255 284 (accept_3_2 28 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 255 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 255 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 255 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 255 284 (accept_3_2 25 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 255 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 255 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 284 (accept_3_2 22 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 255 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 255 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 255 284 (accept_3_2 19 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 255 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 255 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 284 (accept_3_2 16 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 255 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 255 284
  (Polychromatic418967fa.accept_13_1_8_11_1_724 14 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 255 284 (accept_3_2 13 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 255 284 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 255 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 284 (accept_3_2 10 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 255 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 255 284 (accept_3_2 7 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  255 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 255 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 284 (accept_3_2 4 255 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 255 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 284 (accept_3_2 1 255 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255
  284)))))))))))))))))))))))))))))) (allB_succ' 31 254 284 (Eq.refl Bool.true) (allA_succ_of_gcd 30 254 284 2 15 127 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 254 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 254 284 2 14 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 254 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 254 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 254 284 2 13 127 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 254 284 (accept_3_2 25 254 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 254 284 2 12 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 254 284 (Polychromatic418967fa.accept_12_11_2_8_1_511
  23 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 254 284 2 11 127 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 254 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 254 284 2 10 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 254 284 (accept_3_2 19 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 254 284 2 9 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 254 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 254 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 254 284 2 8 127 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 254 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 254 284 2 7 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 254 284 (accept_3_2 13 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 254 284 2 6 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 254 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 254 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 254 284 2 5 127 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 254 284
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 254 284 2 4 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 254 284 (accept_3_2 7 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 254 284 2 3 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 254 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 254 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 254 284 2 2 127 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 254 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 254 284 2 1 127 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 254 284 (accept_3_2 1 254 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  284))))))))))))))))))))))))))))))) (allB_succ' 32 253 284 (Eq.refl Bool.true) (allA_of_3_0 32 253 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 252 284 (Eq.refl Bool.true) (allA_succ_of_gcd 32 252 284 4 8 63 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 252 284
  (accept_3_2 31 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 252 284 2 15 126 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 252 284
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 252 284 4 7 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 252 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 252 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 252 284 2 13 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 252 284 (accept_3_2 25 252 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 252 284 4 6 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 252 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 252
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 252 284 2 11 126 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 252 284
  (Polychromatic418967fa.accept_19_2_5_18_1_10863 21 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 252 284 4 5 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 252 284 (accept_3_2 19 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 252 284 2 9 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 252 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 252 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 252 284 4 4 63 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 252 284
  (Polychromatic418967fa.accept_17_15_14_12_1_1973 15 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 252 284 2 7 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 252 284 (accept_3_2 13 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 252 284 4 3 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 252 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 252 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 252 284 2 5 126 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 252 284
  (Polychromatic418967fa.accept_15_9_12_14_1_963 9 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 252 284 4 2 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 252 284 (accept_3_2 7 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252
  284 2 3 126 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  252 284 (Polychromatic418967fa.accept_24_5_12_20_1_3817 5 252 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 252 284 4 1 63 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 252 284 (Polychromatic418967fa.accept_13_3_5_11_1_716 3 252 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 284 2 1 126 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 284 (accept_3_2 1 252 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 252 284))))))))))))))))))))))))))))))))) (allB_succ' 34 251 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 33 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 251 284 (Polychromatic418967fa.accept_13_6_4_11_1_282
  32 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 251 284 (accept_3_2 31
  251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 251 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 251 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 251 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 251 284 (accept_3_2 28 251 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 251 284 (Polychromatic418967fa.accept_7_5_6_4_1_117
  26 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 251 284 (accept_3_2 25
  251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 251 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 251 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 251 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 251 284 (accept_3_2 22 251 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 251 284 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 251 284 (accept_3_2 19
  251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 251 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 251 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 284 (accept_3_2 16 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 251 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 251 284 (accept_3_2 13 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 251 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 251 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 284 (accept_3_2 10 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 251 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 284
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 251 284 (accept_3_2 7 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  251 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 251 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 284 (accept_3_2 4 251 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 251 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 284 (accept_3_2 1 251 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  284)))))))))))))))))))))))))))))))))) (allB_succ' 35 250 284 (Eq.refl Bool.true) (allA_of_3_0 35 250 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 249 284 (Eq.refl Bool.true) (allA_succ_of_accept 35 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 249 284 (accept_3_2 34 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 249 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 249 284 (Polychromatic418967fa.accept_24_8_9_20_1_7244 32 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 249 284 (accept_3_2 31 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 249 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 249 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 249 284 (accept_3_2 28 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 249 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 249 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 284 (accept_3_2 25 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 249 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 284 (accept_3_2 22 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 249 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 249 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 249 284 (accept_3_2 19 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 249 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 249 284 (accept_3_2 16 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 249 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 249 284 (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 284 (accept_3_2 13 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 249 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 284 (accept_3_2 10 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  249 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 249 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 284 (accept_3_2 7 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 249 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 284 (accept_3_2 4 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 249 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 284 (accept_3_2 1 249 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 284)))))))))))))))))))))))))))))))))))) (allB_succ' 37 248 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 248 284 4 9 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 248 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 35 248 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 248 284 2 17 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 248 284 (Polychromatic418967fa.accept_13_7_1_11_1_732
  33 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 248 284 4 8 62 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 248 284
  (accept_3_2 31 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 248 284 2 15 124 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 248 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 248 284 4 7 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 248 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 248 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 248 284 2 13 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 248 284 (accept_3_2 25 248 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 248 284 4 6 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 248 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 248
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 248 284 2 11 124 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 248 284
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 248 284 4 5 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 248 284 (accept_3_2 19 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  248 284 2 9 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 248 284 (Polychromatic418967fa.accept_16_1_8_12_1_405 17 248 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 248 284 4 4 62 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 248 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15
  248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 248 284 2 7 124 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 248 284 (accept_3_2 13
  248 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 248 284 4 3 62 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 248 284
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 248 284 2 5 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 248 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 248 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 248 284 4 2 62 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 248 284 (accept_3_2 7 248 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 248 284 2 3 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 248 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 5
  248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 248 284 4 1 62 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 248 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 248 284 2 1 124 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 248 284 (accept_3_2 1 248 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  284))))))))))))))))))))))))))))))))))))) (allB_succ' 38 247 284 (Eq.refl Bool.true) (allA_of_3_0 38 247 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 246 284 (Eq.refl Bool.true) (allA_succ_of_gcd 38 246 284 2 19 123 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 246 284
  (accept_3_2 37 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 246 284 2 18 123 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 246 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 246 284 2 17 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 246 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 246 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 246 284 2 16 123 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 246 284 (accept_3_2 31 246 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 246 284 2 15 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 246 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29
  246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 246 284 2 14 123 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 246 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 246 284 2 13 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 246 284 (accept_3_2 25 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 246 284 2 12 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 246 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 23 246 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 246 284 2 11 123 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 246 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 246 284 2 10 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 246 284 (accept_3_2 19 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 284 2 9 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 246 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 246 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 284 2 8 123 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 246 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 246 284 2 7 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 246 284 (accept_3_2 13 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 284 2 6 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 246 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 284 2 5 123 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 246 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 246 284 2 4 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 246 284 (accept_3_2 7 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 284 2 3 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 246 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 284 2 2 123 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 246 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 246 284 2 1 123 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 246 284 (accept_3_2 1 246 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246
  284))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 245 284 (Eq.refl Bool.true) (allA_succ_of_accept 39 245 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 245 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 245 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 245 284 (accept_3_2 37 245 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 245 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 245 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 245 284 (accept_3_2 34 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 245 284 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 245 284 (accept_3_2 31 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 245 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 245 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 245 284
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 245 284 (accept_3_2 28 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 245 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 245 284 (accept_3_2 25 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 245 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 245 284 (accept_3_2 22 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 245 284 (Polychromatic418967fa.accept_16_4_5_12_1_2749 20 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 245 284 (accept_3_2 19 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 284 (Polychromatic418967fa.accept_21_18_14_11_1_7035 18
  245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 245 284 (accept_3_2 16 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 245 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 284 (accept_3_2 13 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 245 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 284
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 245 284 (accept_3_2 10 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 245 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 284 (accept_3_2 7 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 245 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 284
  (Polychromatic418967fa.accept_17_5_7_12_1_1951 5 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 284 (accept_3_2 4 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 245 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 284 (accept_3_2 1 245 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 284)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 244 284 (Eq.refl
  Bool.true) (allA_of_3_0 41 244 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 243 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 243 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 243 284 (accept_3_2 40 243 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 243 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 243 284
  (Polychromatic418967fa.accept_23_15_13_8_1_12655 38 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 243 284 (accept_3_2 37 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 243 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 243 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 243 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 284 (accept_3_2 34 243 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 284 (Polychromatic418967fa.accept_13_7_9_11_1_705
  33 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 243 284 (accept_3_2 31 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 243 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 284 (accept_3_2 28 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 243 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 284
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 284 (accept_3_2 25 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 284 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 284 (accept_3_2 22 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 243 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 284 (accept_3_2 19 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 284 (accept_3_2 16 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 243 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 14 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 284 (accept_3_2 13 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 284 (Polychromatic418967fa.accept_19_12_15_18_1_9544 12 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 243 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 284 (accept_3_2 10 243 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 243 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 284 (accept_3_2 7 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 284 (accept_3_2 4 243 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 3 243 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 284 (accept_3_2 1 243 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  284)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 242 284 (Eq.refl Bool.true) (allA_succ_of_gcd 42 242 284
  2 21 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  242 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 242 284 2 20 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 242 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 242 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 242 284 2 19 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 242 284 (accept_3_2 37 242 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 242 284 2 18 121 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 242 284
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 242 284 2 17 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 242 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 242 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 242 284 2 16 121 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 242 284 (accept_3_2 31 242 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 242 284 2 15 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 242 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29
  242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 242 284 2 14 121 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 242 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 242 284 2 13 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 242 284 (accept_3_2 25 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 242 284 2 12 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 242 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 242 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 242 284 2 11 121 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 242 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 242 284 2 10 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 242 284 (accept_3_2 19 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 242 284 2 9 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 242 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 242 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 284 2 8 121 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 284 2 7 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 284 (accept_3_2 13 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 284 2 6 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 242 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 284 2 5 121 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 284
  (Polychromatic418967fa.accept_13_9_8_11_1_725 9 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 284 2 4 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 284 (accept_3_2 7 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 284 2 3 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 242 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 284 2 2 121 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 284 2 1 121 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 284 (accept_3_2 1 242 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  284))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 241 284 (Eq.refl Bool.true) (allA_of_3_0 44 241 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 240 284 (Eq.refl Bool.true) (allA_succ_of_gcd 44 240 284 4 11
  60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 240 284
  (accept_3_2 43 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 240 284 2 21 120 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 240 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 240 284 4 10 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 240 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 240 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 240 284 2 19 120 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 240 284 (accept_3_2 37 240 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 240 284 4 9 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 240 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35
  240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 240 284 2 17 120 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 240 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 240 284 4 8 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 240 284 (accept_3_2 31 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  240 284 2 15 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 240 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 240 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 240 284 4 7 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 240 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27
  240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 284 2 13 120 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 240 284
  (accept_3_2 25 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 240 284 4 6 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 240 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 240 284 2 11 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 240 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 240 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 240 284 4 5 60 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 240 284 (accept_3_2 19 240 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 284 2 9 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17
  240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 240 284 4 4 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 240 284
  (Polychromatic418967fa.accept_19_15_12_18_1_6634 15 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 240 284 2 7 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 240 284 (accept_3_2 13 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 240 284 4 3 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 240 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 240 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 284 2 5 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9
  240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 284 4 2 60 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 284 (accept_3_2 7
  240 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 284 2 3 120 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 240 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 284 4 1 60 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 240 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 240 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 284 2 1 120 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 284 (accept_3_2 1 240 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 240 284))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 239 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 239 284
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 239 284 (accept_3_2 43 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 239 284 (Polychromatic418967fa.accept_13_3_5_11_1_716 42 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 239 284 (Polychromatic418967fa.accept_19_3_11_18_1_2709 41 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 239 284 (accept_3_2 40 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 239 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 239 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 239 284 (accept_3_2 37 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 239 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 239 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 239 284 (accept_3_2 34 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 239 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 32 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 239 284 (accept_3_2 31 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 239 284 (Polychromatic418967fa.accept_17_13_1_12_1_7893 30 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 239 284 (Polychromatic418967fa.accept_13_3_5_11_1_716 29 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 239 284 (accept_3_2 28 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 239 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 239 284 (accept_3_2 25 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 239 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 239 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 284 (accept_3_2 22 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 239 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 284
  (Polychromatic418967fa.accept_13_7_5_11_1_1927 20 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 239 284 (accept_3_2 19 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 239 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 239 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 284 (accept_3_2 16 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 239 284 (accept_3_2 13 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 239 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 284 (accept_3_2 10 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 284 (accept_3_2 7 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 284 (accept_3_2 4 239 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 239 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 284 (accept_3_2 1 239 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  284)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 238 284 (Eq.refl Bool.true) (allA_of_3_0 47 238 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 237 284 (Eq.refl Bool.true) (allA_succ_of_accept 47 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 237 284 (accept_3_2 46 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 237 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 237 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 237 284 (accept_3_2 43 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 237 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 237 284 (accept_3_2 40 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 237 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 237 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 237 284 (accept_3_2 37 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 237 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 237 284 (accept_3_2 34 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 237 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 237 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 237 284 (accept_3_2 31 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 237 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 237 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 237 284 (accept_3_2 28 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 237 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 237 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 237 284 (accept_3_2 25 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 237 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 237 284 (accept_3_2 22 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 237 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 237 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 284 (accept_3_2 19 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 237 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 284 (accept_3_2 16 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 237 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 237 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 284 (accept_3_2 13 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 237 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 284 (accept_3_2 10 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  237 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 237 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 284 (accept_3_2 7 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 237 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 284 (accept_3_2 4 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  237 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 237 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 237 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 284 (accept_3_2 1 237 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 237 284)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 236 284 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 236 284 4 12 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 236 284 (Polychromatic418967fa.accept_18_11_2_14_1_3351 47 236 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 236 284 2 23 118 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 236 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 236 284 4 11 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 236 284 (accept_3_2 43 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 236 284 2 21 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 236 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 236 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 236 284 4 10 59 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 236 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 236 284 2 19 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 236 284 (accept_3_2 37 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 236 284 4 9 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 236 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 236 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 236 284 2 17 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 236 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 236 284 4 8 59 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 236 284 (accept_3_2 31
  236 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 236 284 2 15 118 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 236 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 236 284 4 7 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 236 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 236 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 236 284 2 13 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 236 284 (accept_3_2 25 236 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 236 284 4 6 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 236 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 236 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 236 284 2 11 118 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 236 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 236 284 4 5 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 236 284 (accept_3_2 19 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  236 284 2 9 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 236 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 236 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 284 4 4 59 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 236 284 2 7 118 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 236 284 (accept_3_2 13
  236 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 236 284 4 3 59 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 236 284
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 11 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 236 284 2 5 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 236 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 236 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 284 4 2 59 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 284 (accept_3_2 7 236 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 284 2 3 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5
  236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 284 4 1 59 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 284 2 1 118 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 284 (accept_3_2 1 236 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  284))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 235 284 (Eq.refl Bool.true) (allA_of_3_0 50 235
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 234 284 (Eq.refl Bool.true) (allA_succ_of_gcd 50 234 284 2
  25 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 234
  284 (accept_3_2 49 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 234 284 2 24 117 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 234 284
  (Polychromatic418967fa.accept_19_9_6_18_1_730 47 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 234 284 2 23 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 234 284 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 234 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 234 284 2 22 117 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 234 284 (accept_3_2 43 234 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 234 284 2 21 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 234 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 234 284 2 20 117 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 234 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 234 284 2 19 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 234 284 (accept_3_2 37 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 234 284 2 18 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 234 284 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 234 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 234 284 2 17 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 234 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 234 284 2 16 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 234 284 (accept_3_2 31 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 234 284 2 15 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 234 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 234 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 234 284 2 14 117 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 234 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 234 284 2 13 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 234 284 (accept_3_2 25 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 234 284 2 12 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 234 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 234 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 234 284 2 11 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 234 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 234 284 2 10 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 234 284 (accept_3_2 19 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 284 2 9 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 234 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 284 2 8 117 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 234 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 234 284 2 7 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 234 284 (accept_3_2 13 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 284 2 6 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 284 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 234 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 284 2 5 117 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 234 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 234 284 2 4 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 234 284 (accept_3_2 7 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 284 2 3 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 284 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 234 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 284 2 2 117 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 234 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 234 284 2 1 117 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 234 284 (accept_3_2 1 234 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  284))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 233 284 (Eq.refl Bool.true) (allA_succ_of_accept
  51 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 233 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 233 284 (accept_3_2 49 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 233 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 233 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 233 284 (accept_3_2 46 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 233 284 (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 233 284 (accept_3_2 43 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 233 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 233 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 233 284 (accept_3_2 40 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 233 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 233 284 (accept_3_2 37 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 233 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 233 284
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 233 284 (accept_3_2 34 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 233 284 (Polychromatic418967fa.accept_19_13_5_18_1_8106 32 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 233 284 (accept_3_2 31 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 233 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 233 284
  (Polychromatic418967fa.accept_8_5_1_4_1_628 29 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 233 284 (accept_3_2 28 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 233 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 284 (accept_3_2 25 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 284
  (Polychromatic418967fa.accept_13_10_12_11_1_731 23 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 233 284 (accept_3_2 22 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 233 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 284 (accept_3_2 19 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 284 (Polychromatic418967fa.accept_11_7_2_9_1_480
  18 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 284
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 233 284 (accept_3_2 16 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 284 (accept_3_2 13 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 233 284 (accept_3_2 10 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 233 284 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 284 (accept_3_2 7 233 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 233 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 284 (accept_3_2 4 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 233 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 284 (accept_3_2 1 233 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 284)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 232 284
  (Eq.refl Bool.true) (allA_of_3_0 53 232 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 231 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 231 284 (accept_3_2 52 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 231 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 231 284
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 231 284 (accept_3_2 49 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 231 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 284 (accept_3_2 46 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 231 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 231 284 (accept_3_2 43 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 231 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 284 (accept_3_2 40 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 231 284 (accept_3_2 37 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 231 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 284 (accept_3_2 34 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 284 (Polychromatic418967fa.accept_19_14_3_18_1_6675 33 231 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 284
  (Polychromatic418967fa.accept_23_9_1_8_1_17421 32 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 284 (accept_3_2 31 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 231 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 284 (accept_3_2 28 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 284 (accept_3_2 25 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 284 (accept_3_2 22 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 284 (accept_3_2 19 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 284 (accept_3_2 16 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 231 284 (accept_3_2 13 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 231 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 231 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 231 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 284 (accept_3_2 10 231 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 284 (Polychromatic418967fa.accept_15_9_6_14_1_2627
  9 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 284 (accept_3_2 7 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 284 (accept_3_2 4 231 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 231 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 284 (accept_3_2 1 231 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 230 284 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 230 284 2 27 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 230 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 230 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 230 284 2 26 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 230 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 51
  230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 230 284 2 25 115 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 230 284
  (accept_3_2 49 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 230 284 2 24 115 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 230 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 230 284 2 23 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 230 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 230 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 230 284 2 22 115 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 230 284 (accept_3_2 43 230 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 230 284 2 21 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 230 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  41 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 230 284 2 20 115 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 230 284
  (Polychromatic418967fa.accept_15_9_5_14_1_973 39 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 230 284 2 19 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 230 284 (accept_3_2 37 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 230 284 2 18 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 230 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 230 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 230 284 2 17 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 230 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 230 284 2 16 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 230 284 (accept_3_2 31 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 230 284 2 15 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 230 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 230 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 230 284 2 14 115 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 230 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 230 284 2 13 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 230 284 (accept_3_2 25 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 230 284 2 12 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 230 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 230 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 230 284 2 11 115 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 230 284
  (Polychromatic418967fa.accept_13_8_9_11_1_1265 21 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 230 284 2 10 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 230 284 (accept_3_2 19 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 230 284 2 9 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 230 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 230 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 284 2 8 115 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 284
  (Polychromatic418967fa.accept_13_2_9_11_1_258 15 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 284 2 7 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 284 (accept_3_2 13 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 284 2 6 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 230 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 284 2 5 115 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 284 2 4 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 284 (accept_3_2 7 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 284 2 3 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 230 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 284 2 2 115 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 284 2 1 115 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 284 (accept_3_2 1 230 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 229 284 (Eq.refl Bool.true) (allA_of_3_0 56
  229 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 228 284 (Eq.refl Bool.true) (allA_succ_of_gcd 56 228
  284 4 14 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  228 284 (accept_3_2 55 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 228 284 2 27 114 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 228 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 228 284 4 13 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 228 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 228 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 228 284 2 25 114 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 228 284 (accept_3_2 49 228 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 228 284 4 12 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 228 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47
  228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 228 284 2 23 114 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 228 284
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 45 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 228 284 4 11 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 228 284 (accept_3_2 43 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 228 284 2 21 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 228 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 228 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 228 284 4 10 57 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 228 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 228 284 2 19 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 228 284 (accept_3_2 37 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 228 284 4 9 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 228 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 228 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 228 284 2 17 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 228 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 284 4 8 57 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 284 (accept_3_2 31
  228 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 284 2 15 114 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 228 284 4 7 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 228 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 27 228 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 228 284 2 13 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 284 (accept_3_2 25 228 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 284 4 6 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 284 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 228
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 284 2 11 114 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 228 284 4 5 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 228 284 (accept_3_2 19 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  228 284 2 9 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 228 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 284 4 4 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 284 2 7 114 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 284 (accept_3_2 13
  228 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 284 4 3 57 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 228 284 2 5 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 228 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 228 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 284 4 2 57 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 284 (accept_3_2 7 228 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 284 2 3 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 284 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 228 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 284 4 1 57 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 284
  (Polychromatic418967fa.accept_13_3_7_11_1_1904 3 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 284 2 1 114 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 284 (accept_3_2 1 228 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 227 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 227 284 (Polychromatic418967fa.accept_13_4_6_11_1_2017 56 227
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 227 284 (accept_3_2 55 227
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 227 284
  (Polychromatic418967fa.accept_25_4_2_9_1_10596 54 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 227 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 227 284 (accept_3_2 52 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 227 284 (Polychromatic418967fa.accept_7_1_3_4_1_128
  50 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 227 284 (accept_3_2 49
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 227 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 227 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 227 284 (accept_3_2 46 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 227 284 (Polychromatic418967fa.accept_9_8_2_5_1_237
  44 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 227 284 (accept_3_2 43
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 227 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 227 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 227 284 (accept_3_2 40 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 227 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  38 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 284 (accept_3_2 37
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 227 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 227 284 (accept_3_2 34 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 284 (Polychromatic418967fa.accept_10_2_7_4_1_967
  32 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 284 (accept_3_2 31
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 227 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 284 (accept_3_2 28 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 284 (Polychromatic418967fa.accept_9_8_2_5_1_237
  26 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 284 (accept_3_2 25
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 227 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 284 (accept_3_2 22 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 284 (Polychromatic418967fa.accept_7_6_3_4_1_294
  20 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 284 (accept_3_2 19
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 284
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 227 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 284 (accept_3_2 16 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 284 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 284 (accept_3_2 13
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 227 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 284 (accept_3_2 10 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 284 (accept_3_2 7 227
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 227 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 284 (accept_3_2 4 227 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 227 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 227 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  227 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 284 (accept_3_2 1 227
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 226 284 (Eq.refl Bool.true) (allA_of_3_0
  59 226 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 225 284 (Eq.refl Bool.true) (allA_succ_of_accept 59
  225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 225 284 (accept_3_2 58 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 225 284 (Polychromatic418967fa.accept_18_3_9_14_1_2219 57 225 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 225 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 225
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 225 284 (accept_3_2 55 225
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 225 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 225 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 225 284 (accept_3_2 52 225 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 225 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 225 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 225 284
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 50 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 225 284 (accept_3_2 49 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 225 284 (Polychromatic418967fa.accept_21_6_15_11_1_5410 48 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 225 284 (accept_3_2 46 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 225 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 225 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 225 284
  (Polychromatic418967fa.accept_28_16_1_4_1_17420 44 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 225 284 (accept_3_2 43 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 225 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 225 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 284 (accept_3_2 40 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 225 284 (Polychromatic418967fa.accept_10_9_5_4_1_966
  39 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 225 284 (accept_3_2 37 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 225 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 284 (accept_3_2 34 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 225 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 225 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 284
  (Polychromatic418967fa.accept_13_6_4_11_1_282 32 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 225 284 (accept_3_2 31 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 225 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 284 (accept_3_2 28 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 225 284 (Polychromatic418967fa.accept_16_11_1_12_1_1795 27 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 225 284 (accept_3_2 25 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 225 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 284 (accept_3_2 22 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 225 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 284
  (Polychromatic418967fa.accept_13_7_4_11_1_1967 20 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 284 (accept_3_2 19 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 284 (accept_3_2 16 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 284 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 284
  (Polychromatic418967fa.accept_19_14_16_18_1_9534 14 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 225 284 (accept_3_2 13 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 225 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 225 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 284 (accept_3_2 10 225 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 9
  225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 284
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 284 (accept_3_2 7 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 284 (accept_3_2 4 225 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 225 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 284
  (Polychromatic418967fa.accept_13_2_4_11_1_2003 2 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 284 (accept_3_2 1 225 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 224 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 224 284 4 15 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 224 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 59 224 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 224 284 2 29 112 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 224 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 224 284 4 14 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 224 284 (accept_3_2 55 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 224 284 2 27 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 224 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 53 224 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 224 284 4 13 56 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 224 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 224 284 2 25 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 224 284 (accept_3_2 49 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 224 284 4 12 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 224 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 224 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 224 284 2 23 112 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 224 284
  (Polychromatic418967fa.accept_19_7_15_18_1_8132 45 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 224 284 4 11 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 224 284 (accept_3_2 43 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 224 284 2 21 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 224 284 (Polychromatic418967fa.accept_13_2_3_11_1_1287 41 224 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 224 284 4 10 56 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 224 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 224 284 2 19 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 224 284 (accept_3_2 37 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 224 284 4 9 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 224 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 224 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 224 284 2 17 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 224 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 33
  224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 224 284 4 8 56 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 224 284 (accept_3_2 31
  224 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 224 284 2 15 112 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 224 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 224 284 4 7 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 224 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 224 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 224 284 2 13 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 224 284 (accept_3_2 25 224 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 224 284 4 6 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 224
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 284 2 11 112 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 284 4 5 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 224 284 (accept_3_2 19 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  224 284 2 9 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 224 284 (Polychromatic418967fa.accept_22_17_4_20_1_8173 17 224 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 284 4 4 56 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 284 2 7 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 284 (accept_3_2 13 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 284 4 3 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 224 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 224 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 284 2 5 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 284
  (Polychromatic418967fa.accept_19_9_15_18_1_10919 9 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 224 284 4 2 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 284 (accept_3_2 7 224 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 284 2 3 112 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 224 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 284 4 1 56 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  224 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 284 2 1 112 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 284 (accept_3_2 1
  224 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 223 284 (Eq.refl Bool.true)
  (allA_of_3_0 62 223 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 222 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 222 284 2 31 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 222 284 (accept_3_2 61 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 222 284 2 30 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 222 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 222 284 2 29 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 222 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 222 284 2 28 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 222 284 (accept_3_2 55 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 222 284 2 27 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 222 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 222 284 2 26 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 222 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 222 284 2 25 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 222 284 (accept_3_2 49 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 222 284 2 24 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 222 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 222 284 2 23 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 222 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 222 284 2 22 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 222 284 (accept_3_2 43 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 222 284 2 21 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 222 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 222 284 2 20 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 222 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 222 284 2 19 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 222 284 (accept_3_2 37 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 284 2 18 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 284 2 17 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 222 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 222 284 2 16 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 222 284 (accept_3_2 31 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 284 2 15 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 284 2 14 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 222 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 222 284 2 13 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 222 284 (accept_3_2 25 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 284 2 12 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 284 2 11 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 222 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 222 284 2 10 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 222 284 (accept_3_2 19 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 284 2 9 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 284 2 8 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 222 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 222 284 2 7 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 222 284 (accept_3_2 13 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 284 2 6 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 222 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 284 2 5 111 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 222 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 222 284 2 4 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 222 284 (accept_3_2 7 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 284 2 3 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 284 (Polychromatic418967fa.accept_19_5_13_18_1_5249 5 222 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 284 2 2 111 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 222 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 222 284 2 1 111 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 222 284 (accept_3_2 1 222 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 221 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 221 284 (accept_3_2 61 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 221 284
  (Polychromatic418967fa.accept_24_12_5_20_1_14152 60 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 221 284 (Polychromatic418967fa.accept_26_7_13_24_1_17419 59 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 221 284 (accept_3_2 58 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 221 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 221 284
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 56 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 221 284 (accept_3_2 55 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 221 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 221 284 (Polychromatic418967fa.accept_19_15_12_18_1_6634 53
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 221 284 (accept_3_2 52
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 221 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 221 284 (accept_3_2 49 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 221 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 284
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 221 284 (accept_3_2 46 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 221 284 (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 221 284 (accept_3_2 43 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 221 284 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 221 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 221 284 (accept_3_2 40 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 284 (accept_3_2 37 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 221 284
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 221 284 (accept_3_2 34 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 221 284 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 221 284 (accept_3_2 31 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 284 (Polychromatic418967fa.accept_19_11_12_18_1_3893 30
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 284
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 29 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 221 284 (accept_3_2 28 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 284 (accept_3_2 25 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 221 284 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 284
  (Polychromatic418967fa.accept_20_3_1_4_1_7654 23 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 284 (accept_3_2 22 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 284 (Polychromatic418967fa.accept_16_4_13_12_1_1740 20 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 284 (accept_3_2 19 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 284 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 284
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 284 (accept_3_2 16 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 284 (accept_3_2 13 221 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 284 (Polychromatic418967fa.accept_15_12_11_14_1_3464 12
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 284
  (Polychromatic418967fa.accept_18_11_5_14_1_4560 11 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 221 284 (accept_3_2 10 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 284 (accept_3_2 7 221 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 284
  (Polychromatic418967fa.accept_19_6_12_18_1_8141 6 221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 221 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 284 (accept_3_2 4 221 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 221 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 221 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 284 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  221 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 284 (accept_3_2 1 221
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 220 284 (Eq.refl Bool.true)
  (allA_of_3_0 65 220 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 219 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 219 284 (accept_3_2 64 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 219 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 219 284 (Polychromatic418967fa.accept_7_6_2_4_1_291
  62 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 219 284 (accept_3_2 61
  219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 219 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 60 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 284 (accept_3_2 58 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 219 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 219 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 219 284 (accept_3_2 55 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 219 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 284 (accept_3_2 52 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 219 284
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 219 284 (accept_3_2 49 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 219 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 219 284 (accept_3_2 46 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 219 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 219 284 (accept_3_2 43 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 219 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 284 (accept_3_2 40 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 219 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 284 (accept_3_2 37 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 219 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 284 (accept_3_2 34 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 284
  (Polychromatic418967fa.accept_22_10_21_20_1_6534 32 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 219 284 (accept_3_2 31 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 219 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 219 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 284 (accept_3_2 28 219 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 284 (Polychromatic418967fa.accept_7_6_2_4_1_291
  27 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 284 (accept_3_2 25 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 284 (accept_3_2 22 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 219 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 284 (accept_3_2 19 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 284 (accept_3_2 16 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 284
  (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 219 284 (accept_3_2 13 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 219 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 219 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 219 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 284 (accept_3_2 10 219 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361
  9 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 284 (accept_3_2 7 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 284 (accept_3_2 4 219 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 219 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 284 (accept_3_2 1 219 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 218 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 218 284 2 33 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 218 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 218 284 2 32 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 218 284
  (Polychromatic418967fa.accept_19_6_9_18_1_8140 63 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 218 284 2 31 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 218 284 (accept_3_2 61 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 218 284 2 30 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 218 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 218 284 2 29 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 218 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 218 284 2 28 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 218 284 (accept_3_2 55 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 218 284 2 27 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 218 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 218 284 2 26 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 218 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 218 284 2 25 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 218 284 (accept_3_2 49 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 218 284 2 24 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 218 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 218 284 2 23 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 218 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 218 284 2 22 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 218 284 (accept_3_2 43 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 218 284 2 21 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 218 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 218 284 2 20 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 284 2 19 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 284 (accept_3_2 37 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 284 2 18 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 284 2 17 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 218 284 2 16 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 218 284 (accept_3_2 31 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 284 2 15 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 284 2 14 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 284
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 218 284 2 13 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 218 284 (accept_3_2 25 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 284 2 12 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 218 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 284 2 11 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 284 2 10 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 284 (accept_3_2 19 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 284 2 9 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 284 2 8 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 284 2 7 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 284 (accept_3_2 13 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 284 2 6 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 218 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 284 2 5 109 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 284 2 4 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 284 (accept_3_2 7 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 284 2 3 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 218 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 284 2 2 109 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 284 2 1 109 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 284 (accept_3_2 1 218 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 217 284 (Eq.refl Bool.true)
  (allA_of_3_0 68 217 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 216 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 216 284 4 17 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 216 284 (accept_3_2 67 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 216 284 2 33 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 216 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 216 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 216 284 4 16 54 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 216 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 216 284 2 31 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 216 284 (accept_3_2 61 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 216 284 4 15 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 216 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 216 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 216 284 2 29 108 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 216 284
  (Polychromatic418967fa.accept_11_2_7_9_1_890 57 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 216 284 4 14 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 216 284 (accept_3_2 55 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 216 284 2 27 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 216 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 53 216 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 216 284 4 13 54 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 216 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 216 284 2 25 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 216 284 (accept_3_2 49 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 216 284 4 12 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 216 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 216 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 216 284 2 23 108 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 216 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 216 284 4 11 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 216 284 (accept_3_2 43 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 216 284 2 21 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 216 284 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 216 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 216 284 4 10 54 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 216 284
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 216 284 2 19 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 216 284 (accept_3_2 37 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 284 4 9 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 216 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 216 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 284 2 17 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 216 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 216 284 4 8 54 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 284 (accept_3_2 31
  216 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 284 2 15 108 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 284
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 216 284 4 7 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 216 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 216 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 216 284 2 13 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 284 (accept_3_2 25 216 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 284 4 6 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 216 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 284 2 11 108 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 216 284
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 216 284 4 5 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 216 284 (accept_3_2 19 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  216 284 2 9 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 216 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 216 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 284 4 4 54 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 284 2 7 108 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 284 (accept_3_2 13
  216 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 284 4 3 54 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 284
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 216 284 2 5 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 216 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 216 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 284 4 2 54 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 284 (accept_3_2 7 216 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 284 2 3 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5
  216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 284 4 1 54 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 284 2 1 108 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 284 (accept_3_2 1 216 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 215 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 215 284 (Polychromatic418967fa.accept_13_3_7_11_1_1904 68 215
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 215 284 (accept_3_2 67 215
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 215 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 66 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 215 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 215 284 (accept_3_2 64 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 215 284 (Polychromatic418967fa.accept_7_6_5_4_1_297
  62 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 215 284 (accept_3_2 61
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 215 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 60 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 215 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 215 284 (accept_3_2 58 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 215 284 (Polychromatic418967fa.accept_9_2_8_5_1_228
  56 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 215 284 (accept_3_2 55
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 215 284
  (Polychromatic418967fa.accept_15_9_5_14_1_973 54 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 215 284 (Polychromatic418967fa.accept_13_1_7_11_1_702 53 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 215 284 (accept_3_2 52 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 215 284 (Polychromatic418967fa.accept_7_1_5_4_1_134
  50 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 215 284 (accept_3_2 49
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 215 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 215 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 215 284 (accept_3_2 46 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 215 284 (Polychromatic418967fa.accept_7_2_5_4_1_115
  44 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 284 (accept_3_2 43
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 215 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 215 284 (accept_3_2 40 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 284 (Polychromatic418967fa.accept_9_2_8_5_1_228
  38 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 284 (accept_3_2 37
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 215 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 284 (accept_3_2 34 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 284 (Polychromatic418967fa.accept_15_2_5_14_1_61
  32 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 284 (accept_3_2 31
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 215 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 284 (accept_3_2 28 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 284 (Polychromatic418967fa.accept_10_6_5_4_1_571
  26 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 284 (accept_3_2 25
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 284 (accept_3_2 22 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 284 (Polychromatic418967fa.accept_7_6_5_4_1_297
  20 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 284 (accept_3_2 19
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 284
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 215 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 284 (accept_3_2 16 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 284 (Polychromatic418967fa.accept_11_3_6_9_1_1378
  14 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 284 (accept_3_2 13
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 284 (accept_3_2 10 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 284 (accept_3_2 7 215
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 215 284 (Polychromatic418967fa.accept_13_5_7_11_1_3470 5 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 284 (accept_3_2 4 215 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 215 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  215 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 284 (accept_3_2 1 215
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 214 284 (Eq.refl Bool.true)
  (allA_of_3_0 71 214 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 213 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 71 213 284 71 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 70 213 284 (accept_3_2 70 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 213 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 68 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 284 (accept_3_2 67 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 213 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 213 284 (accept_3_2 64 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 213 284 (Polychromatic418967fa.accept_14_7_3_4_1_1816 63 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 62 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 284 (accept_3_2 61 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 284 (Polychromatic418967fa.accept_19_3_4_18_1_3882 60 213 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 213 284 (accept_3_2 58 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 213 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 213 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 284 (accept_3_2 55 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 213 284 (accept_3_2 52 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 213 284 (Polychromatic418967fa.accept_20_11_13_4_1_7573 51 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 213 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 284 (accept_3_2 49 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 284 (accept_3_2 46 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 284 (accept_3_2 43 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 284 (accept_3_2 40 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 284 (accept_3_2 37 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 284 (accept_3_2 34 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 284 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 284 (accept_3_2 31 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 213 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 284 (accept_3_2 28 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 284 (accept_3_2 25 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 284 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 284 (accept_3_2 22 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 284 (accept_3_2 19 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 284 (accept_3_2 16 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 284 (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 284 (accept_3_2 13 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 213 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 284 (accept_3_2 10 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 284 (accept_3_2 7 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 213 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 284 (accept_3_2 4 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 213 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 284 (accept_3_2 1 213 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 212 284 (Eq.refl Bool.true) (allA_succ_of_gcd 72 212 284 4 18 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 212 284
  (Polychromatic418967fa.accept_13_6_4_11_1_282 71 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 212 284 2 35 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 212 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 212 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 212 284 4 17 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 212 284 (accept_3_2 67 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 212 284 2 33 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 212 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814
  65 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 212 284 4 16 53 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 212 284
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 212 284 2 31 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 212 284 (accept_3_2 61 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 212 284 4 15 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 212 284 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 212 284 2 29 106 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 212 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 212 284 4 14 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 212 284 (accept_3_2 55 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 212 284 2 27 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 212 284 (Polychromatic418967fa.accept_16_5_4_12_1_3800 53 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 212 284 4 13 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 212 284
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 51 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 212 284 2 25 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 212 284 (accept_3_2 49 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 212 284 4 12 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 212 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 212 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 212 284 2 23 106 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 212 284
  (Polychromatic418967fa.accept_13_6_4_11_1_282 45 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 212 284 4 11 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 212 284 (accept_3_2 43 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 212 284 2 21 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 212 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 212 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 284 4 10 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 284
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 284 2 19 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 284 (accept_3_2 37 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 284 4 9 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 212 284 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 212 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 284 2 17 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 33
  212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 212 284 4 8 53 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 212 284 (accept_3_2 31
  212 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 212 284 2 15 106 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 212 284
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 29 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 212 284 4 7 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 212 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 212 284 2 13 106 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 212 284 (accept_3_2 25 212 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 212 284 4 6 53 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 284
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 212 284 2 11 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 212 284 (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 284 4 5 53 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 284 (accept_3_2 19 212 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 284 2 9 106 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 212 284 4 4 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 212 284 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 212 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 212 284 2 7 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 212 284 (accept_3_2 13 212 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 212 284 4 3 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 212 284 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 212
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 284 2 5 106 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 284
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 284 4 2 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 212 284 (accept_3_2 7 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212
  284 2 3 106 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  212 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 212 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 212 284 4 1 53 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 212 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 212 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 284 2 1 106 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 284 (accept_3_2 1 212 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 212
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 211 284 (Eq.refl
  Bool.true) (allA_of_3_0 74 211 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 210 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 210 284 2 37 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 210 284 (accept_3_2 73 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 210 284 2 36 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 210 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 210 284 2 35 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 210 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 210 284 2 34 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 210 284 (accept_3_2 67 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 210 284 2 33 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 210 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 210 284 2 32 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 210 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 210 284 2 31 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 210 284 (accept_3_2 61 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 210 284 2 30 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 210 284 (Polychromatic418967fa.accept_19_2_1_18_1_2660 59 210 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 210 284 2 29 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 210 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 210 284 2 28 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 210 284 (accept_3_2 55 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 284 2 27 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 210 284 2 26 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 210 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 210 284 2 25 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 210 284 (accept_3_2 49 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 284 2 24 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 284 2 23 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 210 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 210 284 2 22 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 210 284 (accept_3_2 43 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 284 2 21 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 210 284 (Polychromatic418967fa.accept_16_9_2_12_1_1800 41 210 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 284 2 20 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 210 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 210 284 2 19 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 210 284 (accept_3_2 37 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 284 2 18 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 284 2 17 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 210 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 210 284 2 16 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 210 284 (accept_3_2 31 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 284 2 15 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 284 2 14 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 210 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 210 284 2 13 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 210 284 (accept_3_2 25 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 284 2 12 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 23 210 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 284 2 11 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 210 284
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 210 284 2 10 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 210 284 (accept_3_2 19 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 284 2 9 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 284 2 8 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 210 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 210 284 2 7 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 284 (accept_3_2 13 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 284 2 6 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 210 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 284 2 5 105 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 210 284 2 4 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 210 284 (accept_3_2 7 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 284 2 3 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 284 (Polychromatic418967fa.accept_19_5_1_18_1_12184 5 210 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 284 2 2 105 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 210 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 210 284 2 1 105 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 210 284 (accept_3_2 1 210 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 209 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 209 284 (Polychromatic418967fa.accept_12_2_5_8_1_159
  74 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 209 284 (accept_3_2 73
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 209 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 72 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 209 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 209 284 (accept_3_2 70 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 209 284 (Polychromatic418967fa.accept_7_5_6_4_1_117
  68 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 209 284 (accept_3_2 67
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 209 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 209 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 209 284 (accept_3_2 64 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 209 284 (Polychromatic418967fa.accept_9_8_2_5_1_237
  62 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 284 (accept_3_2 61
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 209 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 209 284 (accept_3_2 58 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 209 284 (Polychromatic418967fa.accept_16_8_1_12_1_984
  56 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 284 (accept_3_2 55
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 209 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 209 284 (accept_3_2 52 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 209 284 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 284 (accept_3_2 49
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 209 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 209 284 (accept_3_2 46 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 44
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 284 (accept_3_2 43
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 209 284 (Polychromatic418967fa.accept_17_7_5_12_1_1997 41 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 284 (accept_3_2 40 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 38
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 284 (accept_3_2 37
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 284
  (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 284 (accept_3_2 34 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 284
  (Polychromatic418967fa.accept_27_5_20_14_1_17398 32 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 209 284 (accept_3_2 31 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 209 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 209 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 209 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 284 (accept_3_2 28 209 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 284 (accept_3_2 25 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 284 (accept_3_2 22 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 284
  (Polychromatic418967fa.accept_13_7_1_11_1_732 20 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 284 (accept_3_2 19 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 284 (accept_3_2 16 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 284 (accept_3_2 13 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 284 (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 284 (accept_3_2 10 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 284 (accept_3_2 7 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 284 (accept_3_2 4 209 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 284 (accept_3_2 1 209 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 208 284 (Eq.refl
  Bool.true) (allA_of_3_0 77 208 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 207 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 207 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 207 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 207 284 (accept_3_2 76 207 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 207 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 207 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 207 284
  (Polychromatic418967fa.accept_27_20_18_14_1_2231 74 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 207 284 (accept_3_2 73 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 207 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 207 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 207 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 207 284 (accept_3_2 70 207 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 207 284
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 69 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 207 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 68 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 284 (accept_3_2 67 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 207 284 (accept_3_2 64 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 207 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 284 (accept_3_2 61 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 207 284 (accept_3_2 58 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 207 284 (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 207 284 (Polychromatic418967fa.accept_13_4_12_11_1_5362 56 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 284 (accept_3_2 55 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 207 284 (accept_3_2 52 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 207 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 207 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 284 (accept_3_2 49 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 284 (Polychromatic418967fa.accept_19_10_17_18_1_9555 48
  207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 284 (accept_3_2 46 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 207 284 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 284 (Polychromatic418967fa.accept_19_6_17_18_1_8117 44 207 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 284 (accept_3_2 43 207 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967
  42 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 284 (accept_3_2 40 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 284 (Polychromatic418967fa.accept_25_13_7_9_1_17418 38 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 284 (accept_3_2 37 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 284 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 284 (accept_3_2 34 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 284 (accept_3_2 31 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 284 (accept_3_2 28 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 284 (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 284 (accept_3_2 25 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 284 (accept_3_2 22 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 284 (Polychromatic418967fa.accept_13_7_12_11_1_1911 20 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 284 (accept_3_2 19 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 284 (accept_3_2 16 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 284 (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 284 (Polychromatic418967fa.accept_13_1_12_11_1_728 14 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 284 (accept_3_2 13 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 207
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 284 (accept_3_2 10 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 284 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 284 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 284 (accept_3_2 7 207 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 207 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 284
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 284 (accept_3_2 4 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 207 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 207 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 284 (accept_3_2 1 207 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 206 284 (Eq.refl Bool.true) (allA_succ_of_gcd 78 206 284 2 39 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 206 284
  (Polychromatic418967fa.accept_12_5_2_8_1_172 77 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 206 284 2 38 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 206 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 206 284 2 37 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 206 284 (accept_3_2 73 206 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 206 284 2 36 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 206 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71
  206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 206 284 2 35 103 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 206 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 206 284 2 34 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 206 284 (accept_3_2 67 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 206 284 2 33 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 206 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 206 284 2 32 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 206 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 206 284 2 31 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 206 284 (accept_3_2 61 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 206 284 2 30 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 206 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 206 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 206 284 2 29 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 206 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 206 284 2 28 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 206 284 (accept_3_2 55 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 206 284 2 27 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 206 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 206 284 2 26 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 206 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 206 284 2 25 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 206 284 (accept_3_2 49 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 206 284 2 24 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 206 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 284 2 23 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 284 2 22 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 284 (accept_3_2 43 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 284 2 21 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 284 2 20 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 284 2 19 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 284 (accept_3_2 37 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 284 2 18 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 284 2 17 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 284 2 16 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 284 (accept_3_2 31 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 284 2 15 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 284 2 14 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 284 2 13 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 284 (accept_3_2 25 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 284 2 12 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 206 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 284 2 11 103 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 284 2 10 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 284 (accept_3_2 19 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 284 2 9 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 284 2 8 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 284 2 7 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 284 (accept_3_2 13 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 284 2 6 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 284 2 5 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 284
  (Polychromatic418967fa.accept_19_9_16_18_1_3887 9 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 284 2 4 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 284 (accept_3_2 7 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 284 2 3 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 206 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 284 2 2 103 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 3 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 284 2 1 103 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 284 (accept_3_2 1 206 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 205 284 (Eq.refl
  Bool.true) (allA_of_3_0 80 205 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 204 284 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 204 284 4 20 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 204 284 (accept_3_2 79 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 204 284 2 39 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 204 284 (Polychromatic418967fa.accept_19_1_14_18_1_3919 77 204 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 204 284 4 19 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 204 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 75 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 204 284 2 37 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 204 284 (accept_3_2 73 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 204 284 4 18 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 204 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 204 284 2 35 102 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 204 284
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 69 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 204 284 4 17 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 204 284 (accept_3_2 67 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 204 284 2 33 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 204 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 204 284 4 16 51 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 204 284
  (Polychromatic418967fa.accept_18_9_6_14_1_5913 63 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 204 284 2 31 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 204 284 (accept_3_2 61 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 284 4 15 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 204 284 2 29 102 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 204 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 204 284 4 14 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 204 284 (accept_3_2 55 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 284 2 27 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 284 4 13 51 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 204 284
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 204 284 2 25 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 204 284 (accept_3_2 49 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 284 4 12 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 284 2 23 102 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 204 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 204 284 4 11 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 204 284 (accept_3_2 43 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 284 2 21 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 284 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 204 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 284 4 10 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 204 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 204 284 2 19 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 204 284 (accept_3_2 37 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 284 4 9 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 204 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 284 2 17 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 204 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 284 4 8 51 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 284 (accept_3_2 31
  204 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 284 2 15 102 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 204 284 4 7 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 204 284 (Polychromatic418967fa.accept_13_1_9_11_1_703 27 204 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 204 284 2 13 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 284 (accept_3_2 25 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 284 4 6 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 284 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 204
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 284 2 11 102 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 284 4 5 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 284 (accept_3_2 19 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  204 284 2 9 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 204 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 284 4 4 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 284 (Polychromatic418967fa.accept_13_2_9_11_1_258
  15 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 284 2 7 102 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 284
  (accept_3_2 13 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 284 4 3 51 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 284 2 5 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 284 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 284 4 2 51 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 284 (accept_3_2 7 204 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 284 2 3 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 284 4 1 51 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 284 2 1 102 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 284 (accept_3_2 1 204 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 203 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 203 284
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 80 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 203 284 (accept_3_2 79 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 203 284 (Polychromatic418967fa.accept_31_16_17_5_1_17417 78 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 203 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 203 284 (accept_3_2 76 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 203 284 (accept_3_2 73 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 203 284 (Polychromatic418967fa.accept_16_8_11_12_1_962 72 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 203 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 203 284 (accept_3_2 70 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 203 284
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 68 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 203 284 (accept_3_2 67 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 203 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 66 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 203 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 203 284 (accept_3_2 64 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 203 284
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 203 284 (accept_3_2 61 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 203 284 (Polychromatic418967fa.accept_21_18_14_11_1_7035 60 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 59 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 203 284 (accept_3_2 58 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 203 284
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 56 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 203 284 (accept_3_2 55 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 284 (Polychromatic418967fa.accept_15_9_8_14_1_1699 54 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 203 284 (Polychromatic418967fa.accept_13_1_8_11_1_724 53 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 284 (accept_3_2 52 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 203 284 (accept_3_2 49 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 203 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 48 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 284 (accept_3_2 46 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 284
  (Polychromatic418967fa.accept_18_8_5_14_1_3353 44 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 284 (accept_3_2 43 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 284 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 284 (Polychromatic418967fa.accept_20_1_3_4_1_3213 41 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 284 (accept_3_2 40 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 284 (accept_3_2 37 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 284 (Polychromatic418967fa.accept_13_10_8_11_1_1985 36 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 284 (Polychromatic418967fa.accept_13_9_8_11_1_725 35 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 284 (accept_3_2 34 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 284
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 32 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 284 (accept_3_2 31 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 284 (Polychromatic418967fa.accept_13_4_8_11_1_1937 30 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 284 (accept_3_2 28 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 284 (accept_3_2 25 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 284 (accept_3_2 22 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 284
  (Polychromatic418967fa.accept_15_5_8_14_1_432 20 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 284 (accept_3_2 19 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 284 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 284 (accept_3_2 16 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 284 (accept_3_2 13 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 284 (Polychromatic418967fa.accept_19_12_13_18_1_3886 12 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 284 (Polychromatic418967fa.accept_14_11_7_4_1_3449 11 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 284 (accept_3_2 10 203 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 284
  (Polychromatic418967fa.accept_16_8_11_12_1_962 8 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 284 (accept_3_2 7 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 284 (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 284 (accept_3_2 4 203 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 284 (accept_3_2 1 203 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 202 284 (Eq.refl
  Bool.true) (allA_of_3_0 83 202 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 201 284 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 201 284 (accept_3_2 82 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 201 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 81 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 201 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 201 284 (accept_3_2 79 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 201 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 201 284 (accept_3_2 76 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 201 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 201 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 201 284 (accept_3_2 73 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 201 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 284 (accept_3_2 70 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 284
  (Polychromatic418967fa.accept_15_8_6_14_1_975 68 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 201 284 (accept_3_2 67 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 201 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 284 (accept_3_2 64 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 201 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 201 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 201 284 (accept_3_2 61 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 201 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 284 (accept_3_2 58 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 201 284 (accept_3_2 55 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 201 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 284 (accept_3_2 52 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 284 (accept_3_2 49 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 284 (accept_3_2 46 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 284 (accept_3_2 43 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 284 (accept_3_2 40 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 284 (Polychromatic418967fa.accept_11_6_3_9_1_906 39 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 284 (accept_3_2 37 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 284 (accept_3_2 34 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 284
  (Polychromatic418967fa.accept_17_15_14_12_1_1973 32 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 201 284 (accept_3_2 31 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 201 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 201 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 284 (accept_3_2 28 201 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 284 (Polychromatic418967fa.accept_7_6_5_4_1_297
  27 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 284 (accept_3_2 25 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 284 (accept_3_2 22 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 284 (accept_3_2 19 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 284 (accept_3_2 16 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 284
  (Polychromatic418967fa.accept_21_14_12_11_1_3956 14 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 201 284 (accept_3_2 13 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 284 (Polychromatic418967fa.accept_18_12_3_14_1_5919 12 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11
  201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 284 (accept_3_2 10
  201 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 284 (accept_3_2 7 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 201 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5
  201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 284 (accept_3_2 4 201
  284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 284
  (Polychromatic418967fa.accept_16_3_9_12_1_4831 3 201 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 284 (accept_3_2 1 201 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 200 284 (Eq.refl Bool.true) (allA_succ_of_gcd 84 200 284 4 21 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 200 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 83 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 200 284 2 41 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 200 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 81 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 200 284 4 20 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 200 284 (accept_3_2 79 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 200 284 2 39 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 200 284 (Polychromatic418967fa.accept_15_2_5_14_1_61
  77 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 200 284 4 19 50 71
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 200 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 200 284 2 37 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 200 284 (accept_3_2 73 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 200 284 4 18 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 200 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 200 284 2 35 100 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 200 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 200 284 4 17 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 200 284 (accept_3_2 67 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 200 284 2 33 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 200 284 (Polychromatic418967fa.accept_16_1_8_12_1_405 65 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 200 284 4 16 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 200 284
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 200 284 2 31 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 200 284 (accept_3_2 61 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 200 284 4 15 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 200 284 (Polychromatic418967fa.accept_11_4_2_9_1_496 59 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 200 284 2 29 100 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 200 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 200 284 4 14 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 200 284 (accept_3_2 55 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 200 284 2 27 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 200 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 284 4 13 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 200 284 2 25 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 200 284 (accept_3_2 49 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 200 284 4 12 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 200 284 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 200 284 2 23 100 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 200 284
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 45 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 200 284 4 11 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 200 284 (accept_3_2 43 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 200 284 2 21 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 200 284 (Polychromatic418967fa.accept_16_9_8_12_1_979 41 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 284 4 10 50 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 200 284 2 19 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 284 (accept_3_2 37 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 200 284 4 9 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 200 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 200 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 200 284 2 17 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 200 284 4 8 50 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 200 284 (accept_3_2 31
  200 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 200 284 2 15 100 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 200 284
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 200 284 4 7 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 200 284 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 200 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 200 284 2 13 100 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 200 284 (accept_3_2 25 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 200 284 4 6 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 200 284 (Polychromatic418967fa.accept_15_8_5_14_1_986
  23 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 284 2 11 100 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 284 4 5 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 200 284 (accept_3_2 19 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  200 284 2 9 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 200 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 200 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 284 4 4 50 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 15
  200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 200 284 2 7 100 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 200 284 (accept_3_2 13
  200 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 200 284 4 3 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 200 284
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 11 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 200 284 2 5 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 200 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 284 4 2 50 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 284 (accept_3_2 7 200 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 284 2 3 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 200 284 (Polychromatic418967fa.accept_16_5_8_12_1_1766
  5 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 284 4 1 50 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 284 2 1 100 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 284 (accept_3_2 1 200 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 199 284
  (Eq.refl Bool.true) (allA_of_3_0 86 199 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 198 284 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 198 284 2 43 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 198 284 (accept_3_2 85 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 198 284 2 42 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 198 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 198 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 198 284 2 41 99 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 198 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 198 284 2 40 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 198 284 (accept_3_2 79 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 198 284 2 39 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 198 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 77 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 198 284 2 38 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 198 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 75 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 198 284 2 37 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 198 284 (accept_3_2 73 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 198 284 2 36 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 198 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 71 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 198 284 2 35 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 198 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 198 284 2 34 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 198 284 (accept_3_2 67 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 284 2 33 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 198 284 (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 198 284 2 32 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 198 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 198 284 2 31 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 198 284 (accept_3_2 61 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 284 2 30 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 198 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 198 284 2 29 99 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 198 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 198 284 2 28 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 198 284 (accept_3_2 55 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 284 2 27 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 198 284 (Polychromatic418967fa.accept_13_1_3_11_1_1289 53 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 198 284 2 26 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 198 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 198 284 2 25 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 198 284 (accept_3_2 49 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 198 284 2 24 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 198 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 198 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 198 284 2 23 99 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 198 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 198 284 2 22 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 198 284 (accept_3_2 43 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 284 2 21 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 198 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 198 284 2 20 99 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 198 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 39 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 198 284 2 19 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 198 284 (accept_3_2 37 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 284 2 18 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 284 (Polychromatic418967fa.accept_19_16_8_18_1_8139 35 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 198 284 2 17 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 198 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 198 284 2 16 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 198 284 (accept_3_2 31 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 284 2 15 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 284 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 198 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 198 284 2 14 99 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 198 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 198 284 2 13 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 198 284 (accept_3_2 25 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 198 284 2 12 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 198 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 198 284 2 11 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 198 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 198 284 2 10 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 198 284 (accept_3_2 19 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 284 2 9 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 198 284 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 284 2 8 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 284 2 7 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 284 (accept_3_2 13 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 284 2 6 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 284 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 284 2 5 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 284
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 284 2 4 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 284 (accept_3_2 7 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198
  284 2 3 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  198 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 198 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 198 284 2 2 99 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 198 284 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 198 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 284 2 1 99 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 284 (accept_3_2 1 198 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 197 284
  (Eq.refl Bool.true) (allA_succ_of_accept 87 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 197 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 197 284 (accept_3_2 85 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 197 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 197 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 197 284 (accept_3_2 82 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 197 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 197 284 (accept_3_2 79 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 197 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 197 284 (Polychromatic418967fa.accept_19_1_7_18_1_10869 77 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 197 284 (accept_3_2 76 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 197 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 197 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 197 284 (accept_3_2 73 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 197 284 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 197 284 (Polychromatic418967fa.accept_10_1_7_4_1_968 71 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 284 (accept_3_2 70 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 197 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 197 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 197 284 (accept_3_2 67 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 197 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 197 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 65 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 197 284 (accept_3_2 64 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 197 284 (accept_3_2 61 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 197 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 197 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 284 (accept_3_2 58 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 284 (accept_3_2 55 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 284 (accept_3_2 52 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 197 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 284 (accept_3_2 49 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 284 (accept_3_2 46 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 284
  (Polychromatic418967fa.accept_19_6_7_18_1_120 44 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 284 (accept_3_2 43 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 284 (accept_3_2 40 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 284 (accept_3_2 37 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 284 (Polychromatic418967fa.accept_13_10_2_11_1_1920 36 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 284 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 284 (accept_3_2 34 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 197 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 284
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 284 (accept_3_2 31 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 284 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 284 (accept_3_2 28 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 284 (accept_3_2 25 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 284 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 284 (accept_3_2 22 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 284 (accept_3_2 19 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 284 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 284 (accept_3_2 16 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 284 (accept_3_2 13 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 284 (accept_3_2 10 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 284 (accept_3_2 7 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 284 (accept_3_2 4 197 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 197 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 284 (accept_3_2 1 197 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 196 284
  (Eq.refl Bool.true) (allA_of_3_0 89 196 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 195 284 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 195 284 (accept_3_2 88 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 195 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 195 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 195 284 (accept_3_2 85 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 195 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 195 284 (accept_3_2 82 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 195 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 81 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 195 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 80 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 195 284 (accept_3_2 79 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 195 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 195 284 (accept_3_2 76 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 195 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 195 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 195 284 (accept_3_2 73 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 195 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 284 (accept_3_2 70 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 195 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 69 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 195 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 195 284 (accept_3_2 67 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 195 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 284 (accept_3_2 64 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 195 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 284 (accept_3_2 61 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 195 284 (Polychromatic418967fa.accept_21_18_6_11_1_7031 60 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 284 (accept_3_2 58 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 195 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 195 284 (accept_3_2 55 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 195 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 195 284 (accept_3_2 52 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 195 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 284
  (Polychromatic418967fa.accept_20_10_15_4_1_7525 50 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 195 284 (accept_3_2 49 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 195 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 195 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 195 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 284 (accept_3_2 46 195 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 195 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 45
  195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 195 284 (accept_3_2 43 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 195 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 195 284 (accept_3_2 40 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 195 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 284 (accept_3_2 37 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 195 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 284 (accept_3_2 34 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 284
  (Polychromatic418967fa.accept_11_10_8_9_1_492 32 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 284 (accept_3_2 31 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 195 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 284 (accept_3_2 28 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 284 (Polychromatic418967fa.accept_17_10_8_12_1_6559 27 195 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 284 (accept_3_2 25 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 195 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 284 (accept_3_2 22 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 284
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 284 (accept_3_2 19 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 284 (accept_3_2 16 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 284 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 284
  (Polychromatic418967fa.accept_21_14_6_11_1_7071 14 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 195 284 (accept_3_2 13 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 195 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 284 (accept_3_2 10 195 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9
  195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 284
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 284 (accept_3_2 7 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 284 (accept_3_2 4 195 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 284 (accept_3_2 1 195 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 194 284
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 194 284 2 45 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 194 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 194 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 194 284 2 44 97 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 194 284
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 87 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 194 284 2 43 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 194 284 (accept_3_2 85 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 194 284 2 42 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 194 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 194 284 2 41 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 194 284
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 194 284 2 40 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 194 284 (accept_3_2 79 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 194 284 2 39 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 194 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 194 284 2 38 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 194 284
  (Polychromatic418967fa.accept_13_10_12_11_1_731 75 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 194 284 2 37 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 194 284 (accept_3_2 73 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 194 284 2 36 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 194 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 71 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 194 284 2 35 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 194 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 194 284 2 34 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 194 284 (accept_3_2 67 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 194 284 2 33 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 194 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 194 284 2 32 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 194 284
  (Polychromatic418967fa.accept_16_15_2_12_1_1799 63 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 194 284 2 31 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 194 284 (accept_3_2 61 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 194 284 2 30 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 194 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 194 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 194 284 2 29 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 194 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 194 284 2 28 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 194 284 (accept_3_2 55 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 194 284 2 27 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 194 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 194 284 2 26 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 194 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 194 284 2 25 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 194 284 (accept_3_2 49 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 194 284 2 24 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 194 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 194 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 194 284 2 23 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 194 284
  (Polychromatic418967fa.accept_22_1_18_20_1_4946 45 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 194 284 2 22 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 194 284 (accept_3_2 43 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 194 284 2 21 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 194 284 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 194 284 2 20 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 194 284
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 194 284 2 19 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 194 284 (accept_3_2 37 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 194 284 2 18 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 194 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 194 284 2 17 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 194 284
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 33 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 194 284 2 16 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 194 284 (accept_3_2 31 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 194 284 2 15 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 194 284 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 194 284 2 14 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 194 284
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 194 284 2 13 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 194 284 (accept_3_2 25 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 194 284 2 12 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 194 284 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 194 284 2 11 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 194 284
  (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 194 284 2 10 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 194 284 (accept_3_2 19 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 194 284 2 9 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 194 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 194 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 284 2 8 97 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 284
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 284 2 7 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 284 (accept_3_2 13 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 284 2 6 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 194 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 284 2 5 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 284
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 284 2 4 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 284 (accept_3_2 7 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  284 2 3 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 194 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 284 2 2 97 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 284 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 194 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 284 2 1 97 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 284 (accept_3_2 1 194 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 193 284
  (Eq.refl Bool.true) (allA_of_3_0 92 193 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 192 284 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 192 284 4 23 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 192 284 (accept_3_2 91 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 192 284 2 45 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 192 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 89 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 192 284 4 22 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 192 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 87 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 192 284 2 43 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 192 284 (accept_3_2 85 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 192 284 4 21 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 192 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 192 284 2 41 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 192 284
  (Polychromatic418967fa.accept_13_3_10_11_1_1293 81 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 192 284 4 20 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 192 284 (accept_3_2 79 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 192 284 2 39 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 192 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 192 284 4 19 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 192 284
  (Polychromatic418967fa.accept_17_7_5_12_1_1997 75 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 192 284 2 37 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 192 284 (accept_3_2 73 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 192 284 4 18 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 192 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 192 284 2 35 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 192 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 192 284 4 17 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 192 284 (accept_3_2 67 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 284 2 33 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 192 284 4 16 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 192 284
  (Polychromatic418967fa.accept_14_7_10_4_1_130 63 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 192 284 2 31 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 192 284 (accept_3_2 61 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 192 284 4 15 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 192 284 (Polychromatic418967fa.accept_17_8_5_12_1_7925 59 192 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 192 284 2 29 96 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 192 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 192 284 4 14 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 192 284 (accept_3_2 55 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 284 2 27 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 192 284 4 13 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 192 284
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 192 284 2 25 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 192 284 (accept_3_2 49 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 192 284 4 12 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 192 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 192 284 2 23 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 192 284
  (Polychromatic418967fa.accept_25_20_17_9_1_14068 45 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 192 284 4 11 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 192 284 (accept_3_2 43 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 284 2 21 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 192 284 4 10 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 192 284
  (Polychromatic418967fa.accept_15_9_12_14_1_963 39 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 192 284 2 19 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 192 284 (accept_3_2 37 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 192 284 4 9 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 192 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 192 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 192 284 2 17 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 192 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 192 284 4 8 48 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 192 284 (accept_3_2 31
  192 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 192 284 2 15 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 192 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 192 284 4 7 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 192 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 284 2 13 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 284 (accept_3_2 25 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 284 4 6 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 284 (Polychromatic418967fa.accept_19_4_2_18_1_6662 23 192
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 284 2 11 96 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 284
  (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 192 284 4 5 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 284 (accept_3_2 19 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 284 2 9 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 284 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 284 4 4 48 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 284 2 7 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 284 (accept_3_2 13 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 284 4 3 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 192 284 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 192 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 284 2 5 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 284 (Polychromatic418967fa.accept_15_9_12_14_1_963
  9 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 284 4 2 48 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 284 (accept_3_2 7
  192 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 284 2 3 96 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 284
  (Polychromatic418967fa.accept_19_5_2_18_1_2716 5 192 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 192 284 4 1 48 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 192 284 (Polychromatic418967fa.accept_13_3_10_11_1_1293 3 192 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 284 2 1 96 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 284 (accept_3_2 1 192 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 191
  284 (Eq.refl Bool.true) (allA_succ_of_accept 93 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 191 284
  (Polychromatic418967fa.accept_13_1_9_11_1_703 92 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 191 284 (accept_3_2 91 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 191 284 (accept_3_2 88 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 191 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 86 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 191 284 (accept_3_2 85 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 191 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 191 284 (accept_3_2 82 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 191 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 191 284 (accept_3_2 79 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 191 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 191 284 (Polychromatic418967fa.accept_10_7_1_4_1_1447 77 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 191 284 (accept_3_2 76 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 191 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 191 284 (accept_3_2 73 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 191 284 (Polychromatic418967fa.accept_13_7_9_11_1_705 72 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 191 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 191 284 (accept_3_2 70 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 191 284
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 191 284 (accept_3_2 67 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 191 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 191 284 (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 191 284 (accept_3_2 64 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 191 284
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 191 284 (accept_3_2 61 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 191 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 191 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 191 284 (accept_3_2 58 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 191 284
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 56 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 191 284 (accept_3_2 55 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 191 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 191 284 (accept_3_2 52 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 191 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 191 284 (accept_3_2 49 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 191 284 (accept_3_2 46 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 191 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 191 284 (accept_3_2 43 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 191 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 284 (accept_3_2 40 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 191 284 (accept_3_2 37 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 191 284 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 284 (accept_3_2 34 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 284
  (Polychromatic418967fa.accept_19_13_1_18_1_5279 32 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 191 284 (accept_3_2 31 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 191 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 191 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 284 (Polychromatic418967fa.accept_16_13_15_12_1_1748 29
  191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 284 (accept_3_2 28
  191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 284
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 191 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 284 (accept_3_2 25 191 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 191 284 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 284
  (Polychromatic418967fa.accept_18_5_11_14_1_7203 23 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 191 284 (accept_3_2 22 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 284 (accept_3_2 19 191 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 284
  (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 284 (accept_3_2 16 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 284
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 284 (accept_3_2 13 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 284 (accept_3_2 10 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 284
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 284 (accept_3_2 7 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 284 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 284 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 284 (accept_3_2 4 191 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 284
  (Polychromatic418967fa.accept_11_2_4_9_1_484 2 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 284 (accept_3_2 1 191 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 190
  284 (Eq.refl Bool.true) (allA_of_3_0 95 190 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 189 284
  (Eq.refl Bool.true) (allA_succ_of_accept 95 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 189 284 (accept_3_2 94 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 189 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 93 189
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 189 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 92 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 189 284 (accept_3_2 91 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 189 284 (accept_3_2 88 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 189 284 (Polychromatic418967fa.accept_13_9_7_11_1_1292 87 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 189 284
  (Polychromatic418967fa.accept_25_11_14_9_1_15822 86 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 189 284 (accept_3_2 85 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 189 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 84 189 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 189 284 (accept_3_2 82 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 189 284 (Polychromatic418967fa.accept_8_1_5_4_1_388
  81 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 189 284
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 80 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 189 284 (accept_3_2 79 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 189 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 78 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 189 284 (accept_3_2 76 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 189 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 75 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 189 284
  (Polychromatic418967fa.accept_13_9_7_11_1_1292 74 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 189 284 (accept_3_2 73 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 189 284 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 189 284 (accept_3_2 70 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 189 284 (Polychromatic418967fa.accept_13_4_7_11_1_1981 69 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 189 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 68 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 189 284 (accept_3_2 67 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 189 284 (accept_3_2 64 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 189 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 189 284
  (Polychromatic418967fa.accept_11_7_2_9_1_480 62 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 189 284 (accept_3_2 61 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 189 284 (Polychromatic418967fa.accept_18_6_9_14_1_9915 60 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 189 284 (accept_3_2 58 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 189 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 189 284
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 56 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 189 284 (accept_3_2 55 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 189 284 (accept_3_2 52 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 189 284 (Polychromatic418967fa.accept_11_7_2_9_1_480 51 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 189 284
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 189 284 (accept_3_2 49 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 189 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 189 284 (accept_3_2 46 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 189 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 189 284
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 44 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 284 (accept_3_2 43 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 284 (accept_3_2 40 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 284 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 284 (accept_3_2 37 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 189 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 284 (accept_3_2 34 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 284
  (Polychromatic418967fa.accept_24_8_21_20_1_9094 32 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 189 284 (accept_3_2 31 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 189 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 284 (accept_3_2 28 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 284 (Polychromatic418967fa.accept_13_1_7_11_1_702
  27 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 284
  (Polychromatic418967fa.accept_11_4_2_9_1_496 26 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 284 (accept_3_2 25 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 189 284 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 284 (accept_3_2 22 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 284 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 189 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 284
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 284 (accept_3_2 19 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 284 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 284 (accept_3_2 16 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 284 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 284
  (Polychromatic418967fa.accept_13_1_7_11_1_702 14 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 284 (accept_3_2 13 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 284 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 284 (accept_3_2 10 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 284 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 284
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 284 (accept_3_2 7 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 284 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 284 (accept_3_2 4 189 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 284 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 189 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 284
  (Polychromatic418967fa.accept_20_2_9_4_1_4539 2 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 284 (accept_3_2 1 189 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 188
  284 (Eq.refl Bool.true) (allA_succ_of_gcd 96 188 284 4 24 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 188 284 (Polychromatic418967fa.accept_13_4_6_11_1_2017 95 188
  284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 188 284 2 47 94 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 188 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 93 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 188 284 4 23 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 188 284 (accept_3_2 91 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 188 284 2 45 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 188 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 188 284 4 22 47 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 188 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 87 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 188 284 2 43 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 188 284 (accept_3_2 85 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 188 284 4 21 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 188 284 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 188 284 2 41 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 188 284
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 81 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 188 284 4 20 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 188 284 (accept_3_2 79 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 188 284 2 39 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 188 284 (Polychromatic418967fa.accept_18_5_8_14_1_1282 77 188 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 188 284 4 19 47 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 188 284
  (Polychromatic418967fa.accept_7_5_6_4_1_117 75 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 188 284 2 37 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 188 284 (accept_3_2 73 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 188 284 4 18 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 188 284 (Polychromatic418967fa.accept_21_8_20_11_1_7025 71 188 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 188 284 2 35 94 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 188 284
  (Polychromatic418967fa.accept_9_6_8_5_1_837 69 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 188 284 4 17 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 188 284 (accept_3_2 67 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 188 284 2 33 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 188 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 188 284 4 16 47 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 188 284
  (Polychromatic418967fa.accept_19_6_17_18_1_8117 63 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 188 284 2 31 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 188 284 (accept_3_2 61 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 188 284 4 15 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 188 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 188 284 2 29 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 188 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 188 284 4 14 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 188 284 (accept_3_2 55 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 188 284 2 27 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 188 284 (Polychromatic418967fa.accept_22_9_12_20_1_14316 53 188 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 188 284 4 13 47 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 188 284
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 188 284 2 25 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 188 284 (accept_3_2 49 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 188 284 4 12 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 188 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 188 284 2 23 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 188 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 188 284 4 11 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 188 284 (accept_3_2 43 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 188 284 2 21 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 188 284 (Polychromatic418967fa.accept_18_5_8_14_1_1282 41 188 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 188 284 4 10 47 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 188 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 188 284 2 19 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 188 284 (accept_3_2 37 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 188 284 4 9 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 188 284 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 188 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 188 284 2 17 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 188 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 188 284 4 8 47 71 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 188 284 (accept_3_2 31
  188 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 188 284 2 15 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 188 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 188 284 4 7 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 188 284 (Polychromatic418967fa.accept_21_6_20_11_1_7067 27 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 188 284 2 13 94 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 188 284 (accept_3_2 25 188 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 188 284 4 6 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 188 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 284 2 11 94 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 284
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 284 4 5 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 188 284 (accept_3_2 19 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  188 284 2 9 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 188 284 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 188 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 284 4 4 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 284 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 284 2 7 94 142 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 284 (accept_3_2 13
  188 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 284 4 3 47 71 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 284
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 188 284 2 5 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 188 284 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 284 4 2 47 71 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 284 (accept_3_2 7 188 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 284 2 3 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 284 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 188 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 284 4 1 47 71 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 284
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 284 2 1 94 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 284 (accept_3_2 1 188 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  187 284 (Eq.refl Bool.true) (allA_of_3_0 98 187 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 186 284
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 186 284 2 49 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 186 284 (accept_3_2 97 186 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 186 284 2 48 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 186 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 95 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 186 284 2 47 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 186 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 93 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 186 284 2 46 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 186 284 (accept_3_2 91 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 186 284 2 45 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 186 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 89 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 186 284 2 44 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 186 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 186 284 2 43 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 186 284 (accept_3_2 85 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 186 284 2 42 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 186 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 186 284 2 41 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 186 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 186 284 2 40 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 186 284 (accept_3_2 79 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 186 284 2 39 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 186 284 (Polychromatic418967fa.accept_13_12_4_11_1_1925 77 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 186 284 2 38 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 186 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 186 284 2 37 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 186 284 (accept_3_2 73 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 186 284 2 36 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 186 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 186 284 2 35 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 186 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 186 284 2 34 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 186 284 (accept_3_2 67 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 284 2 33 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 284 2 32 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 186 284
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 63 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 186 284 2 31 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 186 284 (accept_3_2 61 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 284 2 30 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 284 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 284 2 29 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 186 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 57 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 186 284 2 28 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 186 284 (accept_3_2 55 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 284 2 27 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 284 2 26 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 284 2 25 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 284 (accept_3_2 49 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 284 2 24 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 284 2 23 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 284 2 22 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 284 (accept_3_2 43 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 284 2 21 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 284 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 284 2 20 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 284 2 19 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 284 (accept_3_2 37 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 284 2 18 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 284 2 17 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 284 2 16 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 284 (accept_3_2 31 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 284 2 15 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 284 2 14 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 284
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 284 2 13 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 284 (accept_3_2 25 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 284 2 12 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 284 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 284 2 11 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 284
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 284 2 10 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 284 (accept_3_2 19 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 284 2 9 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 284 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 284 2 8 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 284
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 284 2 7 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 284 (accept_3_2 13 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 284 2 6 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 284 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 186 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 284 2 5 93 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 284
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 284 2 4 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 284 (accept_3_2 7 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  284 2 3 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 284 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 186 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 284 2 2 93 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 284 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 186 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 284 2 1 93 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 284 (accept_3_2 1 186 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  284))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  185 284 (Eq.refl Bool.true) (allA_succ_of_accept 99 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 185 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 185 284 (accept_3_2 97 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 185 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 96 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 185 284 (Polychromatic418967fa.accept_20_15_5_4_1_4566 95 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 185 284 (accept_3_2 94 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 185 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 92 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 185 284 (accept_3_2 91 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 185 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 185 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 89 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 185 284 (accept_3_2 88 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 185 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 86 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 185 284 (accept_3_2 85 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 185 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 84 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 185 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 83 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 185 284 (accept_3_2 82 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 185 284
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 80 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 185 284 (accept_3_2 79 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 185 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 185 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 77 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 185 284 (accept_3_2 76 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 185 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 185 284 (accept_3_2 73 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 185 284 (Polychromatic418967fa.accept_13_7_3_11_1_280 72 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 185 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 185 284 (accept_3_2 70 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 284
  (Polychromatic418967fa.accept_15_8_5_14_1_986 68 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 185 284 (accept_3_2 67 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 185 284 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 185 284 (Polychromatic418967fa.accept_17_14_15_12_1_1921 65 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 185 284 (accept_3_2 64 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 185 284 (accept_3_2 61 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 185 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 60 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 185 284 (Polychromatic418967fa.accept_10_9_5_4_1_966 59 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 185 284 (accept_3_2 58 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 185 284 (accept_3_2 55 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 185 284 (Polychromatic418967fa.accept_13_2_3_11_1_1287 54 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 185 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 284 (accept_3_2 52 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 284 (accept_3_2 49 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 284 (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 284 (accept_3_2 46 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 284
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 44 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 284 (accept_3_2 43 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 284 (Polychromatic418967fa.accept_19_4_14_18_1_5234 42 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 284 (accept_3_2 40 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 284 (accept_3_2 37 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 284 (Polychromatic418967fa.accept_14_7_3_4_1_1816 35 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 284 (accept_3_2 34 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 284
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 284 (accept_3_2 31 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 284 (Polychromatic418967fa.accept_20_10_5_4_1_7511 30 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 284 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 284 (accept_3_2 28 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 284
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 284 (accept_3_2 25 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 284 (Polychromatic418967fa.accept_15_9_5_14_1_973 24 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 284 (Polychromatic418967fa.accept_13_10_3_11_1_1923 23 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 284 (accept_3_2 22 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 284
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 284 (accept_3_2 19 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 284 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 284 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 284 (accept_3_2 16 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 284 (accept_3_2 13 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 284 (Polychromatic418967fa.accept_22_12_9_20_1_9822 12 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 284 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 284 (accept_3_2 10 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 284
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 284 (accept_3_2 7 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 284 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 284 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 284 (accept_3_2 4 185 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 284 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 284
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 284 (accept_3_2 1 185 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 184 284 (Eq.refl Bool.true) (allA_of_3_0 101 184 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 183
  284 (Eq.refl Bool.true) (allA_succ_of_accept 101 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 183 284 (accept_3_2 100 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 183 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 99
  183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 183 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 98 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 183 284 (accept_3_2 97 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 183 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 96 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 183 284 (accept_3_2 94 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 183 284 (Polychromatic418967fa.accept_11_5_7_9_1_2696 93 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 183 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 183 284 (accept_3_2 91 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 183 284 (Polychromatic418967fa.accept_11_2_7_9_1_890 90 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 284 (accept_3_2 88 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 183 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 87 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 183 284
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 86 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 183 284 (accept_3_2 85 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 183 284 (Polychromatic418967fa.accept_16_4_7_12_1_2734 84 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 284 (accept_3_2 82 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 183 284 (Polychromatic418967fa.accept_13_3_1_11_1_1268 81 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 183 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 183 284 (accept_3_2 79 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 284 (accept_3_2 76 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 183 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 183 284 (accept_3_2 73 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 183 284 (Polychromatic418967fa.accept_13_7_1_11_1_732 72 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 284 (accept_3_2 70 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 183 284 (accept_3_2 67 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 183 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 284 (accept_3_2 64 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 284 (Polychromatic418967fa.accept_18_9_3_14_1_3361 63 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 62 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 183 284 (accept_3_2 61 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 284 (accept_3_2 58 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 284 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 183 284 (accept_3_2 55 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 183 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 284 (accept_3_2 52 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 284
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 50 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 284 (accept_3_2 49 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 183 284 (Polychromatic418967fa.accept_13_9_1_11_1_275 48 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 284 (accept_3_2 46 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 183 284 (accept_3_2 43 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 284 (accept_3_2 40 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 284
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 284 (accept_3_2 37 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 284 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 284 (accept_3_2 34 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 284
  (Polychromatic418967fa.accept_15_2_3_14_1_972 32 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 284 (accept_3_2 31 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 284 (accept_3_2 28 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 284 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 284
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 284 (accept_3_2 25 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 284 (accept_3_2 22 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 284 (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 284 (accept_3_2 19 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 284 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 284 (accept_3_2 16 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 284
  (Polychromatic418967fa.accept_20_14_3_4_1_11915 14 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 183 284 (accept_3_2 13 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 183 284 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 284 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 284 (accept_3_2 10 183 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 284 (Polychromatic418967fa.accept_10_9_3_4_1_985 9
  183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 284
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 284 (accept_3_2 7 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 284 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 284 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 284 (accept_3_2 4 183 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 284 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 284
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 284 (accept_3_2 1 183 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 182 284 (Eq.refl Bool.true) (allA_succ_of_gcd 102 182 284 2 51 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 182 284 (Polychromatic418967fa.accept_12_5_2_8_1_172
  101 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 182 284 2 50 91 142
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 182 284
  (Polychromatic418967fa.accept_19_4_11_18_1_3909 99 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 182 284 2 49 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 182 284 (accept_3_2 97 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 182 284 2 48 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 182 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 95 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 182 284 2 47 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 182 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 93 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 182 284 2 46 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 182 284 (accept_3_2 91 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 182 284 2 45 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 182 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 89 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 182 284 2 44 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 182 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 87 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 182 284 2 43 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 182 284 (accept_3_2 85 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 182 284 2 42 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 182 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 182 284 2 41 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 182 284
  (Polychromatic418967fa.accept_21_18_14_11_1_7035 81 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 182 284 2 40 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 182 284 (accept_3_2 79 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 182 284 2 39 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 77 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 284 2 38 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 182 284 2 37 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 182 284 (accept_3_2 73 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 284 2 36 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 284 2 35 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 182 284 2 34 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 182 284 (accept_3_2 67 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 284 2 33 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 182 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 182 284 2 32 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 284
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 63 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 182 284 2 31 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 182 284 (accept_3_2 61 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 284 2 30 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 284 2 29 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 182 284 2 28 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 182 284 (accept_3_2 55 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 284 2 27 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 284 2 26 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 182 284 2 25 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 182 284 (accept_3_2 49 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 284 2 24 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 284 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 284 2 23 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 284
  (Polychromatic418967fa.accept_19_7_11_18_1_6680 45 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 182 284 2 22 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 182 284 (accept_3_2 43 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 284 2 21 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 284 2 20 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 284 2 19 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 284 (accept_3_2 37 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 284 2 18 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 284 2 17 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 182 284 2 16 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 182 284 (accept_3_2 31 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 284 2 15 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 284 2 14 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 284
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 284 2 13 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 284 (accept_3_2 25 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 284 2 12 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 284 2 11 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 284
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 284 2 10 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 284 (accept_3_2 19 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 284 2 9 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 284 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 182 284 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 284 2 8 91 142 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 284
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 284 2 7 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 284 (accept_3_2 13 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 284 2 6 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 284 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 284 2 5 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 284
  (Polychromatic418967fa.accept_20_9_2_4_1_9093 9 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 284 2 4 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 284 (accept_3_2 7 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  284 2 3 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 284 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 182 284 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 284 2 2 91 142 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 284 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 182 284 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 284 2 1 91 142 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 284 (accept_3_2 1 182 284
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  284)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_284_segment_001))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


