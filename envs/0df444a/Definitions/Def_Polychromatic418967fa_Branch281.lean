-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch281
-- name    : Polychromatic418967fa_Branch281
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:33:56.6228+00:00
-- url     : https://prove2.me/theorems/09aea7f6-4b98-4a26-9a70-2a99c60a5f5a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch281_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_281 : allB 281 281 :=
  allB_succ' 2 280 281 (Eq.refl Bool.true) (allA_of_3_0 2 280 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  279 281 (Eq.refl Bool.true) (allA_succ_of_accept 2 279 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 279 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 279 281 (accept_3_2 1 279 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 279 281))) (allB_succ' 4 278 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 278 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 278 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 278 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 278 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 278 281 (accept_3_2 1 278 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 278 281)))) (allB_succ' 5 277 281 (Eq.refl Bool.true) (allA_of_3_0
  5 277 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 276 281 (Eq.refl Bool.true) (allA_succ_of_accept 5
  276 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 276 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 276 281 (accept_3_2 4 276 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 276 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 276 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 276 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 276 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 276 281 (accept_3_2 1 276 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 276 281)))))) (allB_succ' 7 275 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 275 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 275 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 275 281 (Polychromatic418967fa.accept_19_5_9_15_1_9239 5 275
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 275 281 (accept_3_2 4 275 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 275 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  275 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 275 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 275 281 (accept_3_2 1 275 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275 281)))))))
  (allB_succ' 8 274 281 (Eq.refl Bool.true) (allA_of_3_0 8 274 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 273 281 (Eq.refl Bool.true) (allA_succ_of_accept 8 273 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 273 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 281 (accept_3_2 7 273 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 273 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  273 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 273 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 273 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 273 281 (accept_3_2 4 273 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  273 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 273 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 273 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 273 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 281 (accept_3_2 1 273 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 273 281))))))))) (allB_succ' 10 272 281 (Eq.refl Bool.true) (allA_succ_of_accept 9 272
  281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 272 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 272 281 (Polychromatic418967fa.accept_27_8_2_11_1_5672 8 272 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 272 281 (accept_3_2 7 272 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 272 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 272 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 272 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5
  272 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 272 281 (accept_3_2 4 272
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 272 281 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 272 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 272 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 272 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 272 281 (accept_3_2 1 272 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 272
  281)))))))))) (allB_succ' 11 271 281 (Eq.refl Bool.true) (allA_of_3_0 11 271 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 270 281 (Eq.refl Bool.true) (allA_succ_of_accept 11 270 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 270 281 (accept_3_2 10 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  270 281 (Polychromatic418967fa.accept_19_9_4_15_1_1415 9 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 270 281 (Polychromatic418967fa.accept_19_8_4_15_1_1414 8 270 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 270 281 (accept_3_2 7 270 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 270 281 (Polychromatic418967fa.accept_17_6_15_9_1_1791 6 270
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 270 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 270 281 (accept_3_2 4 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  270 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 270 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 270 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 270 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 270 281 (accept_3_2 1 270 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 270 281)))))))))))) (allB_succ' 13 269 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 12 269 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 269 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 269 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 269 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 269 281 (accept_3_2 10 269 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 269 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9
  269 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 269 281
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 269 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 269 281 (accept_3_2 7 269 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  269 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 269 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 269 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 269 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 281 (accept_3_2 4 269 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 269 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 269 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 269 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 269 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 269 281 (accept_3_2 1 269 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 269
  281))))))))))))) (allB_succ' 14 268 281 (Eq.refl Bool.true) (allA_of_3_0 14 268 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 267 281 (Eq.refl Bool.true) (allA_succ_of_accept 14 267 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 267 281 (accept_3_2 13 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 267 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 267 281 (Polychromatic418967fa.accept_19_11_1_15_1_9263 11 267 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 281 (accept_3_2 10 267 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 267 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 267 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 267 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 267 281 (accept_3_2 7 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  267 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 267 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 267 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 267 281 (accept_3_2 4 267 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 267 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 267 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 267 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 267 281 (accept_3_2 1 267 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267
  281))))))))))))))) (allB_succ' 16 266 281 (Eq.refl Bool.true) (allA_succ_of_accept 15 266 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 266 281 (Polychromatic418967fa.accept_13_1_6_8_1_208 14 266 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 266 281 (accept_3_2 13 266 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 266 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 266 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 266 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 266 281 (accept_3_2 10
  266 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 266 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 266 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 266 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 266 281 (accept_3_2 7 266 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 266 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 266 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 266 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 5
  266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 266 281 (accept_3_2 4 266
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 266 281 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 266 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 266 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 266 281 (accept_3_2 1 266 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266
  281)))))))))))))))) (allB_succ' 17 265 281 (Eq.refl Bool.true) (allA_of_3_0 17 265 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 264 281 (Eq.refl Bool.true) (allA_succ_of_accept 17 264 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 264 281 (accept_3_2 16 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 264 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 264 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 264 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 264 281 (accept_3_2 13 264 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 264 281 (Polychromatic418967fa.accept_13_12_4_8_1_1120 12 264 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 264 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 264 281 (accept_3_2 10 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  264 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 264 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 264 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 264 281 (accept_3_2 7 264 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 264 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 264 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 264 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 264 281 (accept_3_2 4 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  264 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 264 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 264 281 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 264 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 264 281 (accept_3_2 1 264 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 264 281)))))))))))))))))) (allB_succ' 19 263 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 263 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 263 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 263 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 263 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 263 281 (accept_3_2 16 263 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 263 281
  (Polychromatic418967fa.accept_23_15_10_5_1_17292 15 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 263 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 281 (accept_3_2 13 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 263 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 263 281
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 263 281 (accept_3_2 10 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  263 281 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 263 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 281 (accept_3_2 7 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 263 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 263 281 (accept_3_2 4 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  263 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 263 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 263 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 281 (accept_3_2 1 263 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 263 281))))))))))))))))))) (allB_succ' 20 262 281 (Eq.refl Bool.true) (allA_of_3_0 20
  262 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 261 281 (Eq.refl Bool.true) (allA_succ_of_accept 20
  261 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 261 281 (accept_3_2 19 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 261 281 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 261 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 261 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 261 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 261 281 (accept_3_2 16 261 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 261 281 (Polychromatic418967fa.accept_12_3_9_5_1_853
  15 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 261 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 261 281 (accept_3_2 13 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 261 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 261 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 261 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 261 281 (accept_3_2 10 261 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 261 281 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 261 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 261 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 261 281 (accept_3_2 7 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  261 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 261 281 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 261 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 281 (accept_3_2 4 261 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 261 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 261 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 261 281 (accept_3_2 1 261 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261
  281))))))))))))))))))))) (allB_succ' 22 260 281 (Eq.refl Bool.true) (allA_succ_of_accept 21 260 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 260 281 (Polychromatic418967fa.accept_22_20_18_17_1_9616 20 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 260 281 (accept_3_2 19 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 260 281 (Polychromatic418967fa.accept_23_18_7_5_1_7475 18 260 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 260 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 260 281 (accept_3_2 16 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 260 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 260 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 260 281 (accept_3_2 13 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 260 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 260 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 260 281
  (Polychromatic418967fa.accept_16_11_4_9_1_851 11 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 260 281 (accept_3_2 10 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  260 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 260 281 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 260 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 260 281 (accept_3_2 7 260 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 260 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 260 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 260 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 260 281 (accept_3_2 4 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  260 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 260 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 260 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 260 281 (accept_3_2 1 260 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 260 281)))))))))))))))))))))) (allB_succ' 23 259 281 (Eq.refl Bool.true) (allA_of_3_0
  23 259 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 258 281 (Eq.refl Bool.true) (allA_succ_of_accept 23
  258 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 258 281 (accept_3_2 22 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 258 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 258 281 (Polychromatic418967fa.accept_19_1_11_15_1_2459 20 258
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 258 281 (accept_3_2 19 258
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 258 281
  (Polychromatic418967fa.accept_17_1_3_9_1_958 18 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 258 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 258 281 (accept_3_2 16 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 258 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 258 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 258 281 (Polychromatic418967fa.accept_9_5_6_2_1_161
  14 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 258 281 (accept_3_2 13
  258 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 258 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 258 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 258 281 (accept_3_2 10 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 258 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 258 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 258 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 8
  258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 258 281 (accept_3_2 7 258
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 258 281
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 6 258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 258 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 258 281 (accept_3_2 4 258 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 258 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 258 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 258 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2
  258 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 258 281 (accept_3_2 1 258
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 281)))))))))))))))))))))))) (allB_succ' 25 257 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 257 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 257 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 257 281
  (Polychromatic418967fa.accept_19_4_10_15_1_9243 23 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 257 281 (accept_3_2 22 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 257 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 257 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 257 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 257 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 257 281 (accept_3_2 19 257 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 257 281 (Polychromatic418967fa.accept_7_4_5_1_1_418
  18 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 257 281 (accept_3_2 16 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 257 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 257 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 257 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 281 (accept_3_2 13 257 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 257 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 257 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 257 281 (accept_3_2 10 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  257 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 257 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 257 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 281 (accept_3_2 7 257 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 257 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 281
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 257 281 (accept_3_2 4 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  257 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 257 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 257 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 257 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 281 (accept_3_2 1 257 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 257 281))))))))))))))))))))))))) (allB_succ' 26 256 281 (Eq.refl Bool.true)
  (allA_of_3_0 26 256 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 255 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 255 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 255 281 (accept_3_2 25 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 255 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 255 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 255 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 281 (accept_3_2 22
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 255 281
  (Polychromatic418967fa.accept_12_9_3_5_1_423 21 255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 255 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 255 281 (accept_3_2 19 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 255 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 255 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 255 281 (Polychromatic418967fa.accept_9_8_3_2_1_417
  17 255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 281 (accept_3_2 16
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 255 281
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 255 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 281 (accept_3_2 13 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 255 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 255 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 255 281 (accept_3_2 10
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 255 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 281 (accept_3_2 7 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 255 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 255 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 255 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 281 (accept_3_2 4 255
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 255 281
  (Polychromatic418967fa.accept_19_3_8_15_1_2523 3 255 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 255 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 281 (accept_3_2 1 255 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 255 281))))))))))))))))))))))))))) (allB_succ' 28 254 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 254 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 254 281 (Polychromatic418967fa.accept_20_6_14_1_1_8896 26 254
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 254 281 (accept_3_2 25 254
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 254 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 254 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 254 281 (accept_3_2 22 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 254 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 254 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 254 281 (Polychromatic418967fa.accept_7_6_2_1_1_214
  20 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 254 281 (accept_3_2 19
  254 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 254 281
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 254 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 254 281 (accept_3_2 16 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 254 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 254 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 254 281 (Polychromatic418967fa.accept_13_1_7_8_1_1796
  14 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 254 281 (accept_3_2 13
  254 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 254 281
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 254 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 254 281 (accept_3_2 10 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 254 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 254 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 254 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 254 281 (accept_3_2 7 254
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 254 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 254 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 254 281 (accept_3_2 4 254 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 254 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 254 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 254 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221
  2 254 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 254 281 (accept_3_2 1
  254 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254 281)))))))))))))))))))))))))))) (allB_succ' 29 253 281
  (Eq.refl Bool.true) (allA_of_3_0 29 253 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 252 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 252 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 252 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 252 281 (accept_3_2 28 252 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 252 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 252 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 252 281 (accept_3_2 25 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 252 281 (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 252 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 252 281 (accept_3_2 22 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 252 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 252 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 252 281
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 20 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 252 281 (accept_3_2 19 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 252 281 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 252 281 (Polychromatic418967fa.accept_19_17_5_15_1_7921 17 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 252 281 (accept_3_2 16 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 252 281 (Polychromatic418967fa.accept_22_15_10_17_1_17291 15
  252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 252 281
  (Polychromatic418967fa.accept_13_1_5_8_1_207 14 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 252 281 (accept_3_2 13 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 252 281 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 252 281 (Polychromatic418967fa.accept_19_11_5_15_1_2436 11 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 252 281 (accept_3_2 10 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 252 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 252 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 252 281
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 252 281 (accept_3_2 7 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  252 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 252 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 252 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 252 281 (accept_3_2 4 252 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 252 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 252 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 281
  (Polychromatic418967fa.accept_16_2_12_9_1_2568 2 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 252 281 (accept_3_2 1 252 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252
  281)))))))))))))))))))))))))))))) (allB_succ' 31 251 281 (Eq.refl Bool.true) (allA_succ_of_accept 30 251 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 251 281 (Polychromatic418967fa.accept_19_10_4_15_1_3720 29 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 251 281 (accept_3_2 28 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 251 281 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 251 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 251 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 251 281 (accept_3_2 25 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 251 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 251 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 251 281 (accept_3_2 22 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 251 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 251 281
  (Polychromatic418967fa.accept_16_4_11_9_1_1631 20 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 251 281 (accept_3_2 19 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 251 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 251 281 (Polychromatic418967fa.accept_20_17_11_1_1_8865 17 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 281 (accept_3_2 16 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 251 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 251 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 251 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 251 281 (accept_3_2 13 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 251 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 251 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 251 281 (accept_3_2 10 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 251 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 251 281
  (Polychromatic418967fa.accept_19_8_4_15_1_1414 8 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 251 281 (accept_3_2 7 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  251 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 251 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 281 (accept_3_2 4 251 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 251 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 281 (accept_3_2 1 251 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  281))))))))))))))))))))))))))))))) (allB_succ' 32 250 281 (Eq.refl Bool.true) (allA_of_3_0 32 250 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 249 281 (Eq.refl Bool.true) (allA_succ_of_accept 32 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 249 281 (accept_3_2 31 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 249 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 249 281 (Polychromatic418967fa.accept_24_5_9_17_1_8872 29 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 249 281 (accept_3_2 28 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 249 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 249
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 249 281 (accept_3_2 25 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 249 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 249 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 249 281 (accept_3_2 22 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 249 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 249 281 (accept_3_2 19 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 249 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 249 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 281 (accept_3_2 16 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 249 281 (accept_3_2 13 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 249 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 249 281 (Polychromatic418967fa.accept_19_11_2_15_1_5062 11 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 281 (accept_3_2 10 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 281 (Polychromatic418967fa.accept_18_9_15_11_1_5693 9 249
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 249 281 (accept_3_2 7 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  249 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 249 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 281 (accept_3_2 4 249 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 249 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 249 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 281 (accept_3_2 1 249 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249
  281))))))))))))))))))))))))))))))))) (allB_succ' 34 248 281 (Eq.refl Bool.true) (allA_succ_of_accept 33 248 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 248 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 248 281 (accept_3_2 31 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 248 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 248 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 248 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  29 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 248 281 (accept_3_2 28
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 248 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 248 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 248 281 (accept_3_2 25 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 248 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 248 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 248 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 248 281 (accept_3_2 22
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 248 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 248 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 248 281 (accept_3_2 19 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 248 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 248 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 248 281 (Polychromatic418967fa.accept_9_8_5_2_1_422
  17 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 248 281 (accept_3_2 16
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 248 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 248 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 248 281 (accept_3_2 13 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 248 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 248 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 248 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 248 281 (accept_3_2 10
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 248 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 248 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 281 (accept_3_2 7 248 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 248 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 248 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 248 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 281 (accept_3_2 4 248
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 281 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 248 281 (accept_3_2 1 248 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  281)))))))))))))))))))))))))))))))))) (allB_succ' 35 247 281 (Eq.refl Bool.true) (allA_of_3_0 35 247 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 246 281 (Eq.refl Bool.true) (allA_succ_of_accept 35 246 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 246 281 (accept_3_2 34 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 246 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 246 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 246 281 (accept_3_2 31 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 246 281 (Polychromatic418967fa.accept_13_4_12_8_1_197 30 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 246 281
  (Polychromatic418967fa.accept_16_13_6_9_1_2561 29 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 246 281 (accept_3_2 28 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 246 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 246 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 246 281 (accept_3_2 25 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 246 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 246 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 246 281 (accept_3_2 22 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 246 281 (Polychromatic418967fa.accept_14_7_8_1_1_1621 21 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 246 281 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 246 281 (accept_3_2 19 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 246 281 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 246
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 246 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 246 281 (accept_3_2 16 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 246 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 246 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 281 (accept_3_2 13 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 246 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 246 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 246 281 (accept_3_2 10 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  246 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 246 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 281 (accept_3_2 7 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 246 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 281 (accept_3_2 4 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  246 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 246 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 246 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 281 (accept_3_2 1 246 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 246 281)))))))))))))))))))))))))))))))))))) (allB_succ' 37 245 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 245 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 245 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 245 281 (Polychromatic418967fa.accept_13_9_11_8_1_195 35 245
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 245 281 (accept_3_2 34 245
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 245 281
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 245 281 (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 245 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 245 281 (accept_3_2 31 245 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 245 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 245 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 245 281 (accept_3_2 28 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 245 281 (Polychromatic418967fa.accept_13_1_11_8_1_2562 27 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 245 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 245 281 (accept_3_2 25 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 245 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 245
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 281
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 245 281 (accept_3_2 22 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 245 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 245 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 245 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 245 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 245 281 (accept_3_2 19 245 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 245 281
  (Polychromatic418967fa.accept_25_18_20_6_1_17290 18 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 245 281 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 245 281 (accept_3_2 16 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 245 281 (Polychromatic418967fa.accept_17_15_7_9_1_1809 15 245
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 245 281
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 245 281 (accept_3_2 13 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 245 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 281 (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 245 281 (accept_3_2 10 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 245 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 245 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 281
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 245 281 (accept_3_2 7 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  245 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 245 281 (Polychromatic418967fa.accept_17_5_7_9_1_5122 5 245 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 281 (accept_3_2 4 245 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 281 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 245 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 281 (accept_3_2 1 245 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  281))))))))))))))))))))))))))))))))))))) (allB_succ' 38 244 281 (Eq.refl Bool.true) (allA_of_3_0 38 244 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 243 281 (Eq.refl Bool.true) (allA_succ_of_accept 38 243 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 243 281 (accept_3_2 37 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 243 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 243 281 (Polychromatic418967fa.accept_21_14_12_8_1_6833 35 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 281 (accept_3_2 34 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 243 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 243
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 243 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 243 281 (accept_3_2 31 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 243 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 243 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 243 281 (accept_3_2 28 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 243 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 243 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 243 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 281 (accept_3_2 25 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 243 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 243 281 (Polychromatic418967fa.accept_15_8_3_11_1_849 23 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 281 (accept_3_2 22 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 243 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 243
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 281 (accept_3_2 19 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 243 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 243 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 281 (accept_3_2 16 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 243 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 243 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 281 (accept_3_2 13 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 281 (accept_3_2 10 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 281 (accept_3_2 7 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 281 (accept_3_2 4 243 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 243 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 281 (accept_3_2 1 243 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  281))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 242 281 (Eq.refl Bool.true) (allA_succ_of_accept 39 242 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 242 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 242 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 242 281 (accept_3_2 37 242 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 242 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 242 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 242 281 (accept_3_2 34 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 242 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 242 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 242 281 (accept_3_2 31 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 242 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 242 281
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 242 281 (accept_3_2 28 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 242 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 242 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 242 281 (accept_3_2 25 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 242 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 242 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 242 281 (accept_3_2 22 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 242 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 242 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 242 281 (accept_3_2 19 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 242 281 (Polychromatic418967fa.accept_19_18_14_15_1_9277 18
  242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 242 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 242 281 (accept_3_2 16 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 242 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 242 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 281 (accept_3_2 13 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 242 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 242 281 (accept_3_2 10 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  242 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 242 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 281 (accept_3_2 7 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 242 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 242 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 242 281 (accept_3_2 4 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  242 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 242 281 (Polychromatic418967fa.accept_17_2_4_9_1_2791 2 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 242 281 (accept_3_2 1 242 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 242 281)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 241 281 (Eq.refl
  Bool.true) (allA_of_3_0 41 241 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 240 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 240 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 240 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 240 281 (accept_3_2 40 240 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 240 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 240 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 240 281 (Polychromatic418967fa.accept_7_3_2_1_1_225
  38 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 240 281 (accept_3_2 37
  240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 240 281
  (Polychromatic418967fa.accept_11_3_9_6_1_105 36 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 240 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 240 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 240 281 (accept_3_2 34 240 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 240 281 (Polychromatic418967fa.accept_18_15_6_11_1_5651 33 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 240 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 240 281 (accept_3_2 31 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 240 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 240 281 (Polychromatic418967fa.accept_25_4_15_6_1_17289 29 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 240 281 (accept_3_2 28 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 240 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 240 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 240 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 240 281 (accept_3_2 25 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 240 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 240 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 240 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 240 281 (accept_3_2 22 240 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 240 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 240 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 240 281 (accept_3_2 19 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 240 281 (Polychromatic418967fa.accept_19_18_12_15_1_9288 18 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 240 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 240 281 (accept_3_2 16 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 240 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 240
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 240 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 240 281 (accept_3_2 13 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 240 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 240 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 281 (accept_3_2 10 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 240 281 (Polychromatic418967fa.accept_22_9_20_17_1_17288 9 240
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 240 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 240 281 (accept_3_2 7 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  240 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 240 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 240 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 281 (accept_3_2 4 240 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 240 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 240 281
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 240 281 (accept_3_2 1 240 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240
  281)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 239 281 (Eq.refl Bool.true) (allA_succ_of_accept 42 239
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 239 281 (Polychromatic418967fa.accept_25_16_14_6_1_3089 41 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 239 281 (accept_3_2 40 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 239 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 239 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 239 281 (accept_3_2 37 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 239 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 239 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 239 281 (accept_3_2 34 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 239 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 239 281
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 239 281 (accept_3_2 31 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 239 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 239 281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 239 281 (accept_3_2 28 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 239 281 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 239
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 239 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 239 281 (accept_3_2 25 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 239 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 239 281 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 239 281 (accept_3_2 22 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 239 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 239 281
  (Polychromatic418967fa.accept_17_3_1_9_1_9012 20 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 239 281 (accept_3_2 19 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 239 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 239 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 281 (accept_3_2 16 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 239 281 (accept_3_2 13 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 239 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 281 (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 281 (accept_3_2 10 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 281 (Polychromatic418967fa.accept_19_9_11_15_1_6406 9 239
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 281 (accept_3_2 7 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 281 (accept_3_2 4 239 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 239 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 281 (accept_3_2 1 239 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  281))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 238 281 (Eq.refl Bool.true) (allA_of_3_0 44 238 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 237 281 (Eq.refl Bool.true) (allA_succ_of_accept 44 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 237 281 (accept_3_2 43 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 237 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 237 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 237 281 (accept_3_2 40 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 237 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 237 281 (accept_3_2 37 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 237 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 237 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 237 281 (accept_3_2 34 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 237 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 237 281 (accept_3_2 31 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 237 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 237 281 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 281 (accept_3_2 28 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 237
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 237 281 (accept_3_2 25 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 237 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 237 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 281 (accept_3_2 22 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 281 (accept_3_2 19 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 281 (accept_3_2 16 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 281 (accept_3_2 13 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 281 (accept_3_2 10 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 237 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 281 (accept_3_2 7 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 281 (accept_3_2 4 237 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 237 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 281 (accept_3_2 1 237 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  281))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 236 281 (Eq.refl Bool.true) (allA_succ_of_accept 45
  236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 236 281 (Polychromatic418967fa.accept_21_2_5_8_1_433 44 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 236 281 (accept_3_2 43 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 236 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 236
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 236 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 236 281 (accept_3_2 40 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 236 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 236 281 (accept_3_2 37 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 236 281 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 236 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 236 281
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 236 281 (accept_3_2 34 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 236 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 236 281 (accept_3_2 31 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 236 281 (Polychromatic418967fa.accept_23_7_6_5_1_4128 30 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 236 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 236 281 (accept_3_2 28 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 236 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 236 281 (accept_3_2 25 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 236 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 236 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 236 281
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 236 281 (accept_3_2 22 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 236 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 281 (accept_3_2 19 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 236 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 236 281 (accept_3_2 16 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 236 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 281 (accept_3_2 13 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 236 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 236
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 281 (accept_3_2 10 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 281 (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 281 (accept_3_2 7 236 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 236 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 281 (accept_3_2 4 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 281 (accept_3_2 1 236 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 281)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 235 281 (Eq.refl
  Bool.true) (allA_of_3_0 47 235 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 234 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 234 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 234 281 (accept_3_2 46 234 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 234 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 234 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 234 281 (accept_3_2 43 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 234 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 234 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 234 281 (accept_3_2 40 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 234 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 234 281
  (Polychromatic418967fa.accept_17_4_13_9_1_921 38 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 234 281 (accept_3_2 37 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 234 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 234 281 (accept_3_2 34 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 234 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 234 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 234 281 (accept_3_2 31 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 234 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 234 281 (Polychromatic418967fa.accept_19_10_6_15_1_6444 29 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 234 281 (accept_3_2 28 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 234 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 234 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 234 281 (accept_3_2 25 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 234 281 (Polychromatic418967fa.accept_19_5_6_15_1_10686 24 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 234 281 (accept_3_2 22 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 234 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 281
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 234 281 (accept_3_2 19 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 234 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 234 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 281 (accept_3_2 16 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 234 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 234 281
  (Polychromatic418967fa.accept_21_14_3_8_1_3806 14 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 234 281 (accept_3_2 13 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 234 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 281 (accept_3_2 10 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 281
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 234 281 (accept_3_2 7 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  234 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 234 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 281 (accept_3_2 4 234 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 281 (accept_3_2 1 234 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  281)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 233 281 (Eq.refl Bool.true) (allA_succ_of_accept 48
  233 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 233 281 (Polychromatic418967fa.accept_19_9_5_15_1_2544 47 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 233 281 (accept_3_2 46 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 233 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 233 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 233 281
  (Polychromatic418967fa.accept_13_5_12_8_1_198 44 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 233 281 (accept_3_2 43 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 233 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 233 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 233 281 (accept_3_2 40 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 233 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 233 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 233 281 (accept_3_2 37 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 233 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 233 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 233 281 (accept_3_2 34 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 233 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 233 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 233 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 233 281 (accept_3_2 31 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 233 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 233 281 (Polychromatic418967fa.accept_19_10_5_15_1_6443 29 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 233 281 (accept_3_2 28 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 233 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 233 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 233 281
  (Polychromatic418967fa.accept_11_4_2_6_1_389 26 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 233 281 (accept_3_2 25 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 233 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 233 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 281 (accept_3_2 22 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 233 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 233 281 (accept_3_2 19 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 233 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 281 (accept_3_2 16 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 281 (accept_3_2 13 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 281 (Polychromatic418967fa.accept_19_11_5_15_1_2436 11 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 281 (accept_3_2 10 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 233 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 281
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 281 (accept_3_2 7 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 281 (accept_3_2 4 233 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 233 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 281
  (Polychromatic418967fa.accept_10_2_3_1_1_481 2 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 281 (accept_3_2 1 233 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  281))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 232 281 (Eq.refl Bool.true) (allA_of_3_0 50 232
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 231 281 (Eq.refl Bool.true) (allA_succ_of_accept 50 231
  281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 231 281 (accept_3_2 49 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 231 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 231 281 (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 231 281 (accept_3_2 46 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 231 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 231
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 231 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 231 281 (accept_3_2 43 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 231 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 231 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 231 281 (accept_3_2 40 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 231 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 231 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 231 281 (accept_3_2 37 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 231 281 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 231 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 231 281 (accept_3_2 34 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 231 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 231 281 (accept_3_2 31 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 231 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 231 281 (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 281 (accept_3_2 28 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 231
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 231 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 281 (accept_3_2 25 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 281 (accept_3_2 22 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 281 (accept_3_2 19 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 281 (accept_3_2 16 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 231 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 281 (accept_3_2 13 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 281 (accept_3_2 10 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 231 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 281 (accept_3_2 7 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 281 (accept_3_2 4 231 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 231 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 281 (accept_3_2 1 231 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  281))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 230 281 (Eq.refl Bool.true) (allA_succ_of_accept
  51 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 230 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 50 230 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 230 281 (accept_3_2 49 230 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 230 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 230 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 230 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 230 281 (accept_3_2 46 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 230 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 230 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 230 281 (accept_3_2 43 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 230 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 230 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 230 281
  (Polychromatic418967fa.accept_18_5_14_11_1_2073 41 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 230 281 (accept_3_2 40 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 230 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 230
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 230 281 (accept_3_2 37 230
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 230 281
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 230 281 (accept_3_2 34 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 230 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 230 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 230 281 (accept_3_2 31
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 230 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 230 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 230 281 (accept_3_2 28 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 230 281 (Polychromatic418967fa.accept_7_5_6_1_1_407
  26 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 281 (accept_3_2 25
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 230 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 230 281 (accept_3_2 22 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 230 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 230 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 281 (accept_3_2 19
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 281
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 230 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 230 281 (accept_3_2 16 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 230 281 (Polychromatic418967fa.accept_13_1_9_8_1_1734
  14 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 281 (accept_3_2 13
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 230 281 (accept_3_2 10 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 230 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 281 (accept_3_2 7 230
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 281
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 230 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 281 (accept_3_2 4 230 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 230 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2
  230 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 281 (accept_3_2 1 230
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230 281))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 229 281 (Eq.refl Bool.true) (allA_of_3_0 53 229 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 54 228 281 (Eq.refl Bool.true) (allA_succ_of_accept 53 228 281 (Polychromatic418967fa.accept_8_5_4_1_1_111
  53 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 228 281 (accept_3_2 52
  228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 228 281
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 228 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 228 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 228 281 (accept_3_2 49 228 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 228 281 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 228 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 228 281 (accept_3_2 46 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 228 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 228 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 228 281 (accept_3_2 43 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 228 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 228 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 228 281 (accept_3_2 40 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 228 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 39 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 228 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 228 281 (accept_3_2 37 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 228 281 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 228 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 228 281 (accept_3_2 34 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 228 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 228 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 228 281 (accept_3_2 31 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 228 281 (Polychromatic418967fa.accept_16_14_4_9_1_1646 30 228 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 228 281
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 228 281 (accept_3_2 28 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 228 281 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 228 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 281 (accept_3_2 25 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 228 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 228 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 228 281 (accept_3_2 22 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 228 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 228 281 (Polychromatic418967fa.accept_24_20_12_17_1_17287 20 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 281 (accept_3_2 19 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 228 281 (Polychromatic418967fa.accept_20_18_8_1_1_10382 18 228
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 228 281 (accept_3_2 16 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 228 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 228 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 281 (accept_3_2 13 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 281
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 281 (accept_3_2 10 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  228 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 228 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 281 (accept_3_2 7 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 228 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 281 (accept_3_2 4 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  228 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 228 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 228 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 2 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 281 (accept_3_2 1 228 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 228 281)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 227 281
  (Eq.refl Bool.true) (allA_succ_of_accept 54 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 227 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 227 281 (accept_3_2 52 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 227 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 227 281 (accept_3_2 49 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 227 281 (Polychromatic418967fa.accept_20_8_7_1_1_3024 48 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 227 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 227 281 (accept_3_2 46 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 227 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 227 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 227 281 (accept_3_2 43 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 227 281
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 41 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 227 281 (accept_3_2 40 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 227 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 227 281 (accept_3_2 37 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 227 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 227 281
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 227 281 (accept_3_2 34 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 227 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 227 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 281 (accept_3_2 31 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 281
  (Polychromatic418967fa.accept_24_5_11_17_1_7068 29 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 227 281 (accept_3_2 28 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 227 281 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 227 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 227 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 281 (accept_3_2 25 227 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 281 (Polychromatic418967fa.accept_10_4_7_1_1_471
  24 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 281 (accept_3_2 22 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 281 (Polychromatic418967fa.accept_15_6_2_11_1_325 21 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 281 (accept_3_2 19 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 281
  (Polychromatic418967fa.accept_23_17_20_5_1_7458 17 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 227 281 (accept_3_2 16 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 227 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 227 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 281 (accept_3_2 13 227 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 281 (accept_3_2 10 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 281 (Polychromatic418967fa.accept_17_8_6_9_1_7768 8 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 281 (accept_3_2 7 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 281 (accept_3_2 4 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 281 (Polychromatic418967fa.accept_17_3_6_9_1_2761 3 227 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 281 (accept_3_2 1 227 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 281))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 226 281
  (Eq.refl Bool.true) (allA_of_3_0 56 226 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 225 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 225 281 (accept_3_2 55 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 225 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 225 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 225 281
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 225 281 (accept_3_2 52 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 225 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 225 281 (accept_3_2 49 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 225 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 48 225 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 225 281
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 47 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 225 281 (accept_3_2 46 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 225 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 225 281 (accept_3_2 43 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 281 (Polychromatic418967fa.accept_16_10_1_9_1_4622 42 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 281
  (Polychromatic418967fa.accept_19_3_16_15_1_9281 41 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 225 281 (accept_3_2 40 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 225 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 225 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 281 (accept_3_2 37 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 281 (Polychromatic418967fa.accept_10_6_5_1_1_482
  36 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 225 281
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 35 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 225 281 (accept_3_2 34 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 225 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 33 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 281 (accept_3_2 31 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 225 281 (Polychromatic418967fa.accept_17_13_4_9_1_6390 30 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 225 281 (accept_3_2 28 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 225 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 281 (accept_3_2 25 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 225 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 281
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 281 (accept_3_2 22 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 225 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 281 (accept_3_2 19 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 281 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 225 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 281
  (Polychromatic418967fa.accept_21_17_15_8_1_6799 17 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 225 281 (accept_3_2 16 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 225 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 225 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 281 (accept_3_2 13 225 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 281 (Polychromatic418967fa.accept_11_1_5_6_1_397
  12 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 281
  (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 281 (accept_3_2 10 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  225 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 281 (accept_3_2 7 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 225 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 281
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 5 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 281 (accept_3_2 4 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 225 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 281 (accept_3_2 1 225 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 225 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 224 281
  (Eq.refl Bool.true) (allA_succ_of_accept 57 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 224 281
  (Polychromatic418967fa.accept_23_10_17_5_1_5790 56 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 224 281 (accept_3_2 55 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 224 281 (Polychromatic418967fa.accept_21_12_14_8_1_5258 54 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 224 281
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 53 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 224 281 (accept_3_2 52 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 224 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 224 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 224 281 (accept_3_2 49 224 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 224 281 (Polychromatic418967fa.accept_9_3_8_2_1_162
  48 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 224 281
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 224 281 (accept_3_2 46 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 224 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 224 281 (accept_3_2 43 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 224 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 224 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 224 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 224 281 (accept_3_2 40 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 224 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 224 281 (accept_3_2 37 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 224 281 (Polychromatic418967fa.accept_21_15_14_8_1_6826 36 224
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 224 281
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 224 281 (accept_3_2 34 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 224 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 224 281 (accept_3_2 31 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 224 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 224 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 224 281
  (Polychromatic418967fa.accept_27_2_8_11_1_17286 29 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 224 281 (accept_3_2 28 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 224 281 (Polychromatic418967fa.accept_12_2_8_5_1_408 26 224
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 281 (accept_3_2 25 224
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 224 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 224 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 224 281 (accept_3_2 22 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 224 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750
  20 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 281 (accept_3_2 19
  224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 281
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 224 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 281 (accept_3_2 16 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 281 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 281 (accept_3_2 13
  224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 281
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 224 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 281 (accept_3_2 10 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 281
  (Polychromatic418967fa.accept_26_8_16_21_1_17285 8 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 224 281 (accept_3_2 7 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 224 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 224 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 224 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 281 (accept_3_2 4 224 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3
  224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 281
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 281 (accept_3_2 1 224 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 223 281 (Eq.refl Bool.true) (allA_of_3_0
  59 223 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 222 281 (Eq.refl Bool.true) (allA_succ_of_accept 59
  222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 222 281 (accept_3_2 58 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 222 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 222 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 222
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 222 281 (accept_3_2 55 222
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 222 281
  (Polychromatic418967fa.accept_17_3_1_9_1_9012 54 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 222 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 222 281 (accept_3_2 52 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 222 281 (Polychromatic418967fa.accept_9_5_6_2_1_161
  50 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 222 281 (accept_3_2 49
  222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 222 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 222 281 (accept_3_2 46 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 222 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 222 281 (Polychromatic418967fa.accept_9_8_6_2_1_744
  44 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 222 281 (accept_3_2 43
  222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 222 281
  (Polychromatic418967fa.accept_17_8_1_9_1_7738 42 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 222 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 222 281 (accept_3_2 40 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 222 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 222 281 (accept_3_2 37
  222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 222 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 281 (accept_3_2 34 222 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 222 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 222 281 (accept_3_2 31 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 222 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 222 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 281 (accept_3_2 28 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 222 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 222 281 (accept_3_2 25 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 222 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 281 (accept_3_2 22 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 281 (accept_3_2 19 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 222 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 281 (accept_3_2 16 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 222 281 (accept_3_2 13 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 222 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 281 (accept_3_2 10 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 222 281 (accept_3_2 7 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  222 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 222 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 281 (accept_3_2 4 222 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 281
  (Polychromatic418967fa.accept_19_2_13_15_1_9274 2 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 281 (accept_3_2 1 222 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 221 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 221 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 221 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 221 281 (accept_3_2 58 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 221 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57
  221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 221 281
  (Polychromatic418967fa.accept_19_18_12_15_1_9288 56 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 221 281 (accept_3_2 55 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 221 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 221 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 221 281 (accept_3_2 52 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 221 281 (Polychromatic418967fa.accept_9_6_5_2_1_421
  51 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 221 281
  (Polychromatic418967fa.accept_18_14_5_11_1_5676 50 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 221 281 (accept_3_2 49 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 221 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 221 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 221 281 (accept_3_2 46 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 221 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45
  221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 221 281
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 221 281 (accept_3_2 43 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 221 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 221 281 (Polychromatic418967fa.accept_19_3_12_15_1_568 41 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 221 281 (accept_3_2 40 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 221 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 221 281 (accept_3_2 37 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 221 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 221 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 221 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 281 (accept_3_2 34 221 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 221 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 281
  (Polychromatic418967fa.accept_14_4_11_1_1_940 32 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 221 281 (accept_3_2 31 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 221 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 281 (accept_3_2 28 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 221
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 281 (accept_3_2 25 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 281 (Polychromatic418967fa.accept_16_7_13_9_1_1653 23 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 281 (accept_3_2 22 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 221 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 281
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 281 (accept_3_2 19 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 221 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 281 (accept_3_2 16 221 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 221 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 281
  (Polychromatic418967fa.accept_18_14_5_11_1_5676 14 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 221 281 (accept_3_2 13 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 221 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 281 (Polychromatic418967fa.accept_23_11_14_5_1_17284 11
  221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 281 (accept_3_2 10
  221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 281
  (Polychromatic418967fa.accept_23_9_14_5_1_10814 9 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 221 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 281 (accept_3_2 7 221 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 221 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 221 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5
  221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 281 (accept_3_2 4 221
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 281 (Polychromatic418967fa.accept_7_3_4_1_1_71
  3 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 281
  (Polychromatic418967fa.accept_22_2_1_17_1_17283 2 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 281 (accept_3_2 1 221 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 220 281 (Eq.refl Bool.true)
  (allA_of_3_0 62 220 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 219 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 219 281 (accept_3_2 61 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 219 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 219 281 (Polychromatic418967fa.accept_7_3_2_1_1_225
  59 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 219 281 (accept_3_2 58
  219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 219 281
  (Polychromatic418967fa.accept_12_9_3_5_1_423 57 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 219 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 219 281 (accept_3_2 55 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 219 281 (Polychromatic418967fa.accept_9_8_3_2_1_417
  53 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 219 281 (accept_3_2 52
  219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 219 281
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 219 281 (accept_3_2 49 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 219 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 219 281
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 219 281 (accept_3_2 46 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 219 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 219 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 281 (accept_3_2 43 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 219 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 219 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 219 281 (accept_3_2 40 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 219 281 (Polychromatic418967fa.accept_21_18_9_8_1_11479 39 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 281 (accept_3_2 37 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 281 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 219 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 219 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 281 (accept_3_2 34 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 219 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 219 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 281 (accept_3_2 31 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 219 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 219 281
  (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 219 281 (accept_3_2 28 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 219 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 281 (accept_3_2 25 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 219 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 281 (accept_3_2 22 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 219 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 219 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 281 (accept_3_2 19 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 281 (accept_3_2 16 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 219 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 281 (accept_3_2 13 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 219 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 281
  (Polychromatic418967fa.accept_19_11_10_15_1_3741 11 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 281 (accept_3_2 10 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 219 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 219 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 281 (accept_3_2 7 219 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 281 (accept_3_2 4 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  219 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 219 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 219 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 281 (accept_3_2 1 219 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 219 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  218 281 (Eq.refl Bool.true) (allA_succ_of_accept 63 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 218 281
  (Polychromatic418967fa.accept_19_5_9_15_1_9239 62 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 218 281 (accept_3_2 61 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 218 281 (Polychromatic418967fa.accept_19_3_9_15_1_9240 60 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 218 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 218 281 (accept_3_2 58 218 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 218 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 218 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 218 281 (accept_3_2 55 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 218 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 218 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 218 281 (accept_3_2 52 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 218 281
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 50 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 218 281 (accept_3_2 49 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 218 281 (Polychromatic418967fa.accept_15_3_8_11_1_4386 48 218 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 218 281 (accept_3_2 46 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 218 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 218 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 218 281 (accept_3_2 43 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 218 281 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 218 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 41 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 218 281 (accept_3_2 40 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 218 281
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 218 281 (accept_3_2 37 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 218 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 218 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 281 (accept_3_2 34 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 281 (accept_3_2 31 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 281 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 281 (accept_3_2 28 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 218 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 281
  (Polychromatic418967fa.accept_22_4_20_17_1_11187 26 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 218 281 (accept_3_2 25 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 218 281 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 218 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 281 (accept_3_2 22
  218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 218 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 218 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 281 (accept_3_2 19 218 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 218 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 281
  (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 281 (accept_3_2 16 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 281 (accept_3_2 13 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 281 (Polychromatic418967fa.accept_13_12_10_8_1_3343 12 218
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 218 281 (accept_3_2 10 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  218 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 218 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 218 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 281 (accept_3_2 7 218 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 281 (Polychromatic418967fa.accept_19_6_9_15_1_3694 6 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 281
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 281 (accept_3_2 4 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 281 (Polychromatic418967fa.accept_13_2_10_8_1_1126 2 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 281 (accept_3_2 1 218 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 217 281 (Eq.refl Bool.true) (allA_of_3_0 65 217 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 66 216 281 (Eq.refl Bool.true) (allA_succ_of_accept 65 216 281 (Polychromatic418967fa.accept_7_2_6_1_1_73
  65 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 216 281 (accept_3_2 64
  216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 216 281
  (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 216 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 216 281 (accept_3_2 61 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 216 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 216 281
  (Polychromatic418967fa.accept_23_13_9_5_1_17282 59 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 216 281 (accept_3_2 58 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 216 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 216 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 56 216
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 216 281 (accept_3_2 55 216
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 216 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 216 281 (Polychromatic418967fa.accept_23_7_9_5_1_17281 53 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 216 281 (accept_3_2 52 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 216 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 216 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 216 281 (Polychromatic418967fa.accept_15_5_6_11_1_854
  50 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 216 281 (accept_3_2 49
  216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 216 281
  (Polychromatic418967fa.accept_15_3_6_11_1_855 48 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 216 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 216 281 (accept_3_2 46 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 216 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 216 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 281 (accept_3_2 43 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 216 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 216 281 (Polychromatic418967fa.accept_19_3_7_15_1_6419 41 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 281 (accept_3_2 40 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 216 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 216
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 281
  (Polychromatic418967fa.accept_17_4_12_9_1_6379 38 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 216 281 (accept_3_2 37 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 216 281 (Polychromatic418967fa.accept_16_4_8_9_1_4639 36 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 216 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 281 (accept_3_2 34 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 216 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 281 (accept_3_2 31 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 281 (Polychromatic418967fa.accept_22_7_18_17_1_17280 29 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 281 (accept_3_2 28 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 216
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 216 281 (accept_3_2 25 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 216 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 216 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 216 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 281 (accept_3_2 22 216 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 281 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 281
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 281 (accept_3_2 19 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 216 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 281 (accept_3_2 16 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 216
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 281
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 216 281 (accept_3_2 13 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 216 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 281 (Polychromatic418967fa.accept_19_11_7_15_1_14688 11
  216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 281 (accept_3_2 10
  216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 216 281 (Polychromatic418967fa.accept_19_8_7_15_1_13364 8 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 281 (accept_3_2 7 216 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 216 281 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 216 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 281 (accept_3_2 4 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 216 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 216 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 281 (accept_3_2 1 216 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 215 281 (Eq.refl Bool.true) (allA_succ_of_accept 66 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 215 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 215 281
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 215 281 (accept_3_2 64 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 215 281 (Polychromatic418967fa.accept_25_13_15_6_1_6608 63 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 215 281 (accept_3_2 61 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 215 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 215 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 215 281 (accept_3_2 58 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 215 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 215 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 215 281 (accept_3_2 55 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 215 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 215 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 215 281 (accept_3_2 52 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 215 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 215 281 (accept_3_2 49 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 215 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 215 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 215 281 (accept_3_2 46 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 215 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 215 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 281 (accept_3_2 43 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 215 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 281 (accept_3_2 40 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 281 (accept_3_2 37 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 281
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 35 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 281 (accept_3_2 34 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 281 (accept_3_2 31 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 281 (accept_3_2 28 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 281 (accept_3_2 25 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 281 (accept_3_2 22 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 281 (accept_3_2 19 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 281 (accept_3_2 16 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 281 (accept_3_2 13 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 281 (accept_3_2 10 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 281 (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 281 (accept_3_2 7 215 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 281 (accept_3_2 4 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 215 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 281 (accept_3_2 1 215 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 214 281 (Eq.refl Bool.true) (allA_of_3_0 68 214 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 213 281
  (Eq.refl Bool.true) (allA_succ_of_accept 68 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 213 281 (accept_3_2 67 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 213 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 213 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 213 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 213 281 (accept_3_2 64 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 213 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 213 281 (accept_3_2 61 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 213 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 213 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 213 281 (accept_3_2 58 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 213 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 213 281 (accept_3_2 55 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 213 281 (accept_3_2 52 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 213 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 213 281 (accept_3_2 49 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 213 281 (accept_3_2 46 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 213 281 (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 281 (accept_3_2 43 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 281 (accept_3_2 40 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 281 (accept_3_2 37 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 281 (accept_3_2 34 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 281 (accept_3_2 31 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 281
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 281 (accept_3_2 28 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 281 (accept_3_2 25 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 281 (accept_3_2 22 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 281 (accept_3_2 19 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 281 (accept_3_2 16 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 281 (accept_3_2 13 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 281 (accept_3_2 10 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 281 (accept_3_2 7 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 213 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 281 (accept_3_2 4 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 213 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 281 (accept_3_2 1 213 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 212 281 (Eq.refl Bool.true) (allA_succ_of_accept 69 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32
  69 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 212 281
  (Polychromatic418967fa.accept_21_5_2_8_1_5267 68 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 212 281 (accept_3_2 67 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 212 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 212 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 212 281 (accept_3_2 64 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 212 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 212 281 (accept_3_2 61 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 212 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 212 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 212 281 (accept_3_2 58 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 212 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 212 281 (accept_3_2 55 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 212 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 212 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 212 281 (accept_3_2 52 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 212 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 212 281 (accept_3_2 49 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 212 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 212 281 (Polychromatic418967fa.accept_19_9_3_15_1_2429 47 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 212 281 (accept_3_2 46 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 212 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 212 281 (accept_3_2 43 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 212 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 212 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 281 (accept_3_2 40 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 212 281 (accept_3_2 37 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 212 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 212 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 281 (accept_3_2 34 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 281
  (Polychromatic418967fa.accept_27_5_23_11_1_17279 32 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 212 281 (accept_3_2 31 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 212 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 212 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 281 (accept_3_2 28 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 212 281 (accept_3_2 25 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 212 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 212 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 281 (accept_3_2 22 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 212 281 (accept_3_2 19 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 212 281 (Polychromatic418967fa.accept_17_1_8_9_1_1810 18 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 212 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 281 (accept_3_2 16 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 212 281 (accept_3_2 13 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 212 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 212 281 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 281 (accept_3_2 10 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 212 281 (accept_3_2 7 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  212 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 212 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 281 (accept_3_2 4 212 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 281 (accept_3_2 1 212 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 211 281 (Eq.refl Bool.true)
  (allA_of_3_0 71 211 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 210 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 210 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 210 281 (accept_3_2 70 210 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 210 281 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 210 281 (accept_3_2 67
  210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 210 281
  (Polychromatic418967fa.accept_17_15_6_9_1_13743 66 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 210 281 (Polychromatic418967fa.accept_16_1_2_9_1_1607 65 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 210 281 (accept_3_2 64 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 210 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 210 281 (accept_3_2 61 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 210 281 (accept_3_2 58 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 210 281 (Polychromatic418967fa.accept_20_17_10_1_1_11739 57 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 210 281
  (Polychromatic418967fa.accept_23_10_3_5_1_10880 56 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 210 281 (accept_3_2 55 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 210 281 (Polychromatic418967fa.accept_16_6_2_9_1_5897 54 210 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 210 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 210 281 (accept_3_2 52 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 210 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 210 281 (accept_3_2 49 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 210 281 (Polychromatic418967fa.accept_23_2_3_5_1_17278 48 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 210 281 (accept_3_2 46 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 210 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 210 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 210 281 (accept_3_2 43 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 210 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 210 281 (accept_3_2 40 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 281
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 210 281 (accept_3_2 37 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 210 281 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 210 281 (accept_3_2 34 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 210 281 (accept_3_2 31 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 210 281 (Polychromatic418967fa.accept_19_11_1_15_1_9263 30 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 210 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 281 (accept_3_2 28 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 281 (accept_3_2 25 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 281 (accept_3_2 22 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 281 (Polychromatic418967fa.accept_19_2_1_15_1_2494 21 210 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 281
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 20 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 210 281 (accept_3_2 19 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 210 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 210 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 281 (accept_3_2 16 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 281 (accept_3_2 13 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 210 281 (Polychromatic418967fa.accept_16_12_2_9_1_3461 12 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 281 (accept_3_2 10 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 281 (Polychromatic418967fa.accept_18_9_12_11_1_5642 9 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 281 (accept_3_2 7 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  210 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 210 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 281 (accept_3_2 4 210 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 281
  (Polychromatic418967fa.accept_19_2_1_15_1_2494 2 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 281 (accept_3_2 1 210 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 209 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 209 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 209 281 (Polychromatic418967fa.accept_13_6_1_8_1_1116 71 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 209 281 (accept_3_2 70 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 209 281
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 69 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 209 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 209 281 (accept_3_2 67 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 209 281 (Polychromatic418967fa.accept_16_2_1_9_1_2577 66 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 209 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 209 281 (accept_3_2 64 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 209 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 209 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 62 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 209 281 (accept_3_2 61 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 209 281 (Polychromatic418967fa.accept_22_16_11_17_1_12695 60
  209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 209 281
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 209 281 (accept_3_2 58 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 209 281 (Polychromatic418967fa.accept_13_5_1_8_1_1115 57 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 209 281 (Polychromatic418967fa.accept_16_8_1_9_1_847 56 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 209 281 (accept_3_2 55 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 209 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 209 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 209 281
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 209 281 (accept_3_2 52 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 209 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 209 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 50 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 281 (accept_3_2 49 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 281 (accept_3_2 46 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 209 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 281 (accept_3_2 43 209 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 281
  (Polychromatic418967fa.accept_17_7_5_9_1_7763 41 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 281 (accept_3_2 40 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 281 (Polychromatic418967fa.accept_27_12_20_11_1_15534 39 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 38 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 281 (accept_3_2 37 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 281 (Polychromatic418967fa.accept_27_9_20_11_1_5703 36 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 281 (accept_3_2 34 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 281 (accept_3_2 31 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 209 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 281
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 29 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 281 (accept_3_2 28 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 281 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 281 (accept_3_2 25 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 281 (accept_3_2 22 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 281 (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 281 (accept_3_2 19 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 281
  (Polychromatic418967fa.accept_21_17_20_8_1_9938 17 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 209 281 (accept_3_2 16 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 209 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 281 (Polychromatic418967fa.accept_17_14_5_9_1_7766 14 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 281 (accept_3_2 13 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 209 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 281 (accept_3_2 10 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 209 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 209 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 8
  209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 281 (accept_3_2 7 209
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 281
  (Polychromatic418967fa.accept_13_6_1_8_1_1116 6 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 209 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 281 (accept_3_2 4 209 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 209 281 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 209 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 281 (accept_3_2 1 209 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 208 281 (Eq.refl
  Bool.true) (allA_of_3_0 74 208 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 207 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 207 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 207 281 (accept_3_2 73 207 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 207 281 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 207 281
  (Polychromatic418967fa.accept_19_14_17_15_1_3761 71 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 207 281 (accept_3_2 70 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 207 281 (Polychromatic418967fa.accept_11_3_9_6_1_105 69 207 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 207 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 207 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 207 281 (accept_3_2 67 207 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 207 281
  (Polychromatic418967fa.accept_19_8_17_15_1_11952 65 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 207 281 (accept_3_2 64 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 207 281 (Polychromatic418967fa.accept_25_13_7_6_1_17277 63 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62
  207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 207 281 (accept_3_2 61
  207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 281
  (Polychromatic418967fa.accept_14_4_11_1_1_940 60 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 207 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 207 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 207 281 (accept_3_2 58 207 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 207 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 207 281 (accept_3_2 55 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 207 281 (Polychromatic418967fa.accept_13_1_12_8_1_1818 53 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 207 281 (accept_3_2 52 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 207 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 51 207
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 207 281 (accept_3_2 49 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 207 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 48 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 207 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 281 (accept_3_2 46 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 207 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 207 281 (accept_3_2 43 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 207 281 (Polychromatic418967fa.accept_19_3_17_15_1_6459 41 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 281 (accept_3_2 40 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 207 281 (Polychromatic418967fa.accept_19_1_17_15_1_7897 39 207
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 207 281 (accept_3_2 37 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 207 281 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 281 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 281 (accept_3_2 34 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 207 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 281 (accept_3_2 31 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 207 281 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 281 (accept_3_2 28 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 281 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 207
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 281 (accept_3_2 25 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 23 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 281 (accept_3_2 22 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 207
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 281 (accept_3_2 19 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 281 (accept_3_2 16 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 281 (Polychromatic418967fa.accept_18_15_9_11_1_4371 15 207 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 281 (accept_3_2 13 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 281 (Polychromatic418967fa.accept_17_11_3_9_1_6387 11 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 281 (accept_3_2 10 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 207 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 281 (accept_3_2 7 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 281 (accept_3_2 4 207 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 281
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 281 (accept_3_2 1 207 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 206 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 206 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 74
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 206 281 (accept_3_2 73
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 206 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 206 281 (accept_3_2 70 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 206 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  68 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 206 281 (accept_3_2 67
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 206 281
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 206 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 206 281 (accept_3_2 64 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 206 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296
  62 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 206 281 (accept_3_2 61
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 206 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 60 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 206 281 (accept_3_2 58 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 206 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  56 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 206 281 (accept_3_2 55
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 206 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 54 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 206 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 206 281 (accept_3_2 52 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 206 281 (Polychromatic418967fa.accept_9_5_8_2_1_409
  50 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 206 281 (accept_3_2 49
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 206 281
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 281 (accept_3_2 46 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 206 281 (accept_3_2 43
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 206 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 206 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 281 (accept_3_2 40 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 281 (Polychromatic418967fa.accept_17_4_2_9_1_3896
  38 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 206 281 (accept_3_2 37
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 206 281
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 281 (accept_3_2 34 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 206 281 (accept_3_2 31
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 206 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 206 281 (Polychromatic418967fa.accept_13_3_11_8_1_1094 29 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 281 (accept_3_2 28 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  26 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 281 (accept_3_2 25
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 206 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 24 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 281 (accept_3_2 22 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 281 (accept_3_2 19
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 206 281 (Polychromatic418967fa.accept_10_7_6_1_1_486 17 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 281 (accept_3_2 16 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 281 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 281 (accept_3_2 13
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 281 (accept_3_2 10 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 206 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 281 (accept_3_2 7 206
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 206 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 281 (accept_3_2 4 206 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 206 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2
  206 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 281 (accept_3_2 1 206
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 205 281 (Eq.refl
  Bool.true) (allA_of_3_0 77 205 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 204 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 204 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 204 281 (accept_3_2 76 204 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 204 281
  (Polychromatic418967fa.accept_19_17_14_15_1_1403 74 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 204 281 (accept_3_2 73 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 204 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 72 204 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 204 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 204 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 204 281 (accept_3_2 70 204 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111
  69 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 204 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 204 281 (accept_3_2 67 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 204 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 65 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 204 281 (accept_3_2 64 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 204 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 204
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 204 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 204 281 (accept_3_2 61 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 204 281 (Polychromatic418967fa.accept_21_18_15_8_1_8425 60 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 204 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 204 281 (accept_3_2 58 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 204 281
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 56 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 204 281 (accept_3_2 55 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 204 281 (Polychromatic418967fa.accept_21_12_15_8_1_5238 54 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 281 (accept_3_2 52 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 204 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 204 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 204 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 204 281 (accept_3_2 49 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 204 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 281 (accept_3_2 46 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 204 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 204 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 204 281 (accept_3_2 43 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 204 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 42 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 204 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 281 (accept_3_2 40 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 204 281
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 281 (accept_3_2 37 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 204 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 204 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 281 (accept_3_2 34 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 204 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 204 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 204 281 (accept_3_2 31 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 281 (accept_3_2 28 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 204 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 204 281 (accept_3_2 25 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 204 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 204 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 281 (accept_3_2 22 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 281
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 281 (accept_3_2 19 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 204 281 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 204 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 281 (accept_3_2 16 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 204 281 (accept_3_2 13 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 204 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 281 (accept_3_2 10 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 281 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 204 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 204 281 (accept_3_2 7 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  204 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 204 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 281 (accept_3_2 4 204 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 204 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 281
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 281 (accept_3_2 1 204 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 203 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 203 281
  (Polychromatic418967fa.accept_22_11_5_17_1_4659 77 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 203 281 (accept_3_2 76 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 75 203 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 203 281 (accept_3_2 73 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 203 281 (Polychromatic418967fa.accept_10_2_3_1_1_481
  72 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 203 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 203 281 (accept_3_2 70 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 203 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 68 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 203 281 (accept_3_2 67 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 203 281
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 65 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 203 281 (accept_3_2 64 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 203 281 (Polychromatic418967fa.accept_15_3_8_11_1_4386 63 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 203 281 (accept_3_2 61 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 203 281
  (Polychromatic418967fa.accept_17_8_16_9_1_8952 59 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 203 281 (accept_3_2 58 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 203 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 281 (accept_3_2 55 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 203 281 (accept_3_2 52 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 281 (accept_3_2 49 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 281
  (Polychromatic418967fa.accept_17_13_16_9_1_5128 47 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 203 281 (accept_3_2 46 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 203 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 203 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 281 (accept_3_2 43 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 281
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 281 (accept_3_2 40 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 281 (accept_3_2 37 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 281 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 281 (accept_3_2 34 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 281 (accept_3_2 31 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 281
  (Polychromatic418967fa.accept_24_5_11_17_1_7068 29 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 203 281 (accept_3_2 28 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 203 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 203 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 281 (accept_3_2 25 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421
  24 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 281
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 281 (accept_3_2 22 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 281 (Polychromatic418967fa.accept_14_6_7_1_1_78 20 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 281 (accept_3_2 19 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 281 (accept_3_2 16 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 281 (accept_3_2 13 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 281
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 203 281 (accept_3_2 10 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 203 281 (Polychromatic418967fa.accept_19_9_13_15_1_3677 9 203 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 281 (accept_3_2 7 203 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 281
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 281 (accept_3_2 4 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 203 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 281 (accept_3_2 1 203 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 202 281 (Eq.refl Bool.true) (allA_of_3_0 80 202 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 201 281 (Eq.refl Bool.true) (allA_succ_of_accept 80 201 281 (Polychromatic418967fa.accept_6_2_3_5_1_26
  80 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 201 281 (accept_3_2 79
  201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 201 281
  (Polychromatic418967fa.accept_9_6_3_2_1_431 78 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 201 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 201 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 201 281 (accept_3_2 76 201 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 201 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 75 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 201 281 (accept_3_2 73 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 201 281 (Polychromatic418967fa.accept_17_4_14_9_1_5105 72 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 201 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 201 281 (accept_3_2 70 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 201 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 201 281 (accept_3_2 67 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 201 281 (Polychromatic418967fa.accept_15_5_6_11_1_854 65 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 281 (accept_3_2 64 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 201 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 201
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 201 281 (accept_3_2 61 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 201 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 281 (accept_3_2 58 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 281 (Polychromatic418967fa.accept_21_15_12_8_1_5275 57 201 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 201 281 (accept_3_2 55 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 201 281 (Polychromatic418967fa.accept_13_2_6_8_1_1092 54 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 201 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 281 (accept_3_2 52 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 281 (accept_3_2 49 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 281 (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 281 (accept_3_2 46 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 201 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 281 (accept_3_2 43 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 281 (accept_3_2 40 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 281 (accept_3_2 37 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 281 (Polychromatic418967fa.accept_21_15_12_8_1_5275 36 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 281 (accept_3_2 34 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 281 (accept_3_2 31 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 281 (Polychromatic418967fa.accept_11_8_3_6_1_1855 30 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 29 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 281 (accept_3_2 28 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 201 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 281 (accept_3_2 25 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 281 (accept_3_2 22 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 281 (Polychromatic418967fa.accept_17_4_14_9_1_5105 21 201 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 281 (accept_3_2 19 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 281 (accept_3_2 16 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 281 (accept_3_2 13 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 281 (Polychromatic418967fa.accept_17_12_14_9_1_5079 12 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 281 (accept_3_2 10 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 281 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 281 (accept_3_2 7 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 281 (accept_3_2 4 201 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 201 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 281
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 281 (accept_3_2 1 201 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 200 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 200 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 80
  200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 200 281 (accept_3_2 79
  200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 200 281
  (Polychromatic418967fa.accept_17_10_13_9_1_3913 78 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 200 281 (Polychromatic418967fa.accept_13_12_5_8_1_1101 77 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 200 281 (accept_3_2 76 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 200 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 200 281 (accept_3_2 73 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 200 281 (Polychromatic418967fa.accept_17_4_13_9_1_921 72 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 200 281 (Polychromatic418967fa.accept_16_7_8_9_1_9427 71 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 200 281 (accept_3_2 70 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 200 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 200 281 (accept_3_2 67 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 200 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 200 281 (Polychromatic418967fa.accept_16_1_8_9_1_3462 65 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 200 281 (accept_3_2 64 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 200 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 200 281 (accept_3_2 61 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 200 281 (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 200 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 200 281 (accept_3_2 58 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 281
  (Polychromatic418967fa.accept_17_5_13_9_1_9018 56 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 200 281 (accept_3_2 55 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 200 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 200 281 (Polychromatic418967fa.accept_13_1_5_8_1_207 53 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 281 (accept_3_2 52 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 200 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 200 281 (accept_3_2 49 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 200 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 200 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 281 (accept_3_2 46 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 200 281
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 200 281 (accept_3_2 43 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 200 281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 200 281 (Polychromatic418967fa.accept_19_3_10_15_1_9241 41 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 200 281 (accept_3_2 40 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 200 281 (accept_3_2 37 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 200 281 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 200 281 (Polychromatic418967fa.accept_18_17_2_11_1_9749 35 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 281 (accept_3_2 34 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 281 (accept_3_2 31 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 281 (Polychromatic418967fa.accept_19_11_10_15_1_3741 30 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 200 281 (Polychromatic418967fa.accept_13_3_5_8_1_1099 29 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 281 (accept_3_2 28 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 281 (accept_3_2 25 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 281 (Polychromatic418967fa.accept_13_10_5_8_1_2555 23 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 281 (accept_3_2 22 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 281
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 281 (accept_3_2 19 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 281 (Polychromatic418967fa.accept_21_18_11_8_1_5273 18 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 281 (accept_3_2 16 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 281 (accept_3_2 13 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 281 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 281 (accept_3_2 10 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 281
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 281 (accept_3_2 7 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 281 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 281 (accept_3_2 4 200 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 281 (accept_3_2 1 200 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 199 281 (Eq.refl
  Bool.true) (allA_of_3_0 83 199 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 198 281 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 198 281 (accept_3_2 82 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 198 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 198 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 198 281 (accept_3_2 79 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 198 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 78 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 198 281 (Polychromatic418967fa.accept_16_13_6_9_1_2561 77 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 198 281 (accept_3_2 76 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 198 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 198 281
  (Polychromatic418967fa.accept_13_9_3_8_1_573 74 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 198 281 (accept_3_2 73 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 198 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 198 281 (accept_3_2 70 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 198 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 198 281
  (Polychromatic418967fa.accept_15_8_3_11_1_849 68 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 198 281 (accept_3_2 67 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 198 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 198 281 (Polychromatic418967fa.accept_23_19_14_5_1_17226 65 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 198 281 (accept_3_2 64 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 198 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 198 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 198 281 (accept_3_2 61 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 198 281 (Polychromatic418967fa.accept_19_3_8_15_1_2523 60 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 198 281 (accept_3_2 58 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 198 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 57 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 198 281
  (Polychromatic418967fa.accept_20_16_18_1_1_8836 56 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 198 281 (accept_3_2 55 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 198 281 (Polychromatic418967fa.accept_17_3_11_9_1_5100 54 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 198 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 198
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 281 (accept_3_2 52 198
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 198 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 198 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 50 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 198 281 (accept_3_2 49 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 198 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 281 (accept_3_2 46
  198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 198 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 198 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 281 (accept_3_2 43 198 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 198 281 (Polychromatic418967fa.accept_17_8_11_9_1_5099 42 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 198 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 198 281 (accept_3_2 40 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 198 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 281 (accept_3_2 37 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 198 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 198 281 (accept_3_2 34 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 198 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 198 281 (Polychromatic418967fa.accept_23_9_14_5_1_10814 32 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 281 (accept_3_2 31 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 281 (Polychromatic418967fa.accept_25_5_23_6_1_17276 30 198
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 198 281
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 281 (accept_3_2 28 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 198 281 (Polychromatic418967fa.accept_19_7_8_15_1_2448 26 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 281 (accept_3_2 25 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 198 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 198 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 281 (accept_3_2 22 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 198 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 198 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 281 (accept_3_2 19 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 281 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 281 (accept_3_2 16 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 281 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 281 (accept_3_2 13 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 281 (Polychromatic418967fa.accept_19_12_8_15_1_5067 12 198
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 281 (accept_3_2 10 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  198 281 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 198 281 (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 281 (accept_3_2 7 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 198 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 281
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 281 (accept_3_2 4 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  198 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 198 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 281 (accept_3_2 1 198 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 197 281
  (Eq.refl Bool.true) (allA_succ_of_accept 84 197 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 197 281
  (Polychromatic418967fa.accept_23_14_13_5_1_15747 83 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 197 281 (accept_3_2 82 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 197 281 (Polychromatic418967fa.accept_15_6_2_11_1_325 81 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 197 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 80 197
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 197 281 (accept_3_2 79 197
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 197 281
  (Polychromatic418967fa.accept_9_6_8_2_1_410 78 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 197 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 197 281 (accept_3_2 76 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 197 281 (Polychromatic418967fa.accept_10_4_7_1_1_471
  74 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 197 281 (accept_3_2 73
  197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 197 281
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 72 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 197 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 71 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 197 281 (accept_3_2 70 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 197 281 (Polychromatic418967fa.accept_8_4_5_1_1_299
  68 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 197 281 (accept_3_2 67
  197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 197 281
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 197 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 197 281 (accept_3_2 64 197 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 197 281 (Polychromatic418967fa.accept_22_19_21_17_1_6283 63 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 281
  (Polychromatic418967fa.accept_13_10_2_8_1_2603 62 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 197 281 (accept_3_2 61 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 197 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 197 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 281 (accept_3_2 58 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 281
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 281 (accept_3_2 55 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 281 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 281 (Polychromatic418967fa.accept_25_3_22_6_1_17275 53 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 281 (accept_3_2 52 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 197 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 281 (accept_3_2 49 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 281 (Polychromatic418967fa.accept_17_13_10_9_1_946 47 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 281 (accept_3_2 46 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 281 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 197
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 281
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 281 (accept_3_2 43 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 281 (accept_3_2 40 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 281
  (Polychromatic418967fa.accept_11_5_10_6_1_793 38 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 281 (accept_3_2 37 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 281 (accept_3_2 34 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 197 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 281 (accept_3_2 31 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 281 (Polychromatic418967fa.accept_16_13_5_9_1_4682 29 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 281 (accept_3_2 28 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 197
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 281
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 26 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 281 (accept_3_2 25 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 281 (accept_3_2 22 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 281
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 281 (accept_3_2 19 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 281 (Polychromatic418967fa.accept_17_1_10_9_1_3884 18 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 281 (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 281 (accept_3_2 16 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 197 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 281 (accept_3_2 13 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 281 (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 281 (accept_3_2 10 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 197
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 281
  (Polychromatic418967fa.accept_19_8_7_15_1_13364 8 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 281 (accept_3_2 7 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 281 (accept_3_2 4 197 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 197 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 281
  (Polychromatic418967fa.accept_18_2_17_11_1_3178 2 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 281 (accept_3_2 1 197 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 196 281
  (Eq.refl Bool.true) (allA_of_3_0 86 196 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 195 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 195 281 (accept_3_2 85 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 195 281
  (Polychromatic418967fa.accept_23_14_11_5_1_7453 83 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 195 281 (accept_3_2 82 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 195 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 195 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 195 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 195 281 (accept_3_2 79 195 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78
  195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 195 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 77 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 195 281 (accept_3_2 76 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 195 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 195 281 (accept_3_2 73 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 195 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 195 281 (accept_3_2 70 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 195 281 (Polychromatic418967fa.accept_10_9_5_1_1_1325 69 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 281 (accept_3_2 67 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 195 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 195 281 (accept_3_2 64 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 195 281 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 281 (accept_3_2 61 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 281 (Polychromatic418967fa.accept_16_12_3_9_1_5886 60 195 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 195 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 195 281 (accept_3_2 58 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 281 (accept_3_2 55 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 195 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 53 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 281 (accept_3_2 52 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 195 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 281 (accept_3_2 49 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 195 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 195 281 (accept_3_2 46 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 195 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 281 (accept_3_2 43 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 281 (accept_3_2 40 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 281 (accept_3_2 37 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 281 (accept_3_2 34 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 281 (accept_3_2 31 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 281 (accept_3_2 28 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 281 (Polychromatic418967fa.accept_18_9_15_11_1_5693 27 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 281 (accept_3_2 25 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 281 (accept_3_2 22 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 281 (accept_3_2 19 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 281 (accept_3_2 16 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 281 (Polychromatic418967fa.accept_21_15_6_8_1_9888 15 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 281 (accept_3_2 13 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 281
  (Polychromatic418967fa.accept_17_11_8_9_1_8919 11 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 281 (accept_3_2 10 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 281 (accept_3_2 7 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 281 (accept_3_2 4 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 281 (accept_3_2 1 195 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 194 281
  (Eq.refl Bool.true) (allA_succ_of_accept 87 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 194 281
  (Polychromatic418967fa.accept_16_6_2_9_1_5897 86 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 194 281 (accept_3_2 85 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 194 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 194 281 (accept_3_2 82 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 194 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 194 281 (accept_3_2 79 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 194 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 194 281 (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 194 281 (accept_3_2 76 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 194 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 194 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 194 281 (accept_3_2 73 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 194 281 (Polychromatic418967fa.accept_13_7_12_8_1_199 72 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 194 281 (accept_3_2 70 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 194 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 194 281 (accept_3_2 67 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 194 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 194 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 65 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 281 (accept_3_2 64 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 194 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 194 281 (accept_3_2 61 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 194 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 281 (accept_3_2 58 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 281
  (Polychromatic418967fa.accept_11_1_7_6_1_378 56 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 194 281 (accept_3_2 55 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 194 281 (Polychromatic418967fa.accept_16_6_2_9_1_5897 54 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 194 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 281 (accept_3_2 52 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 281
  (Polychromatic418967fa.accept_20_10_14_1_1_5868 50 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 194 281 (accept_3_2 49 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 194 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 194 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 194 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 281 (accept_3_2 46 194 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 281 (accept_3_2 43 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 281 (accept_3_2 40 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 281
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 281 (accept_3_2 37 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 281 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 281 (accept_3_2 34 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 281
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 281 (accept_3_2 31 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 281 (Polychromatic418967fa.accept_19_10_4_15_1_3720 29 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 281 (accept_3_2 28 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 281 (accept_3_2 25 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 281 (accept_3_2 22 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 281
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 281 (accept_3_2 19 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 281 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 281 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 281 (accept_3_2 16 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 281
  (Polychromatic418967fa.accept_13_1_12_8_1_1818 14 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 281 (accept_3_2 13 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 281 (accept_3_2 10 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 281 (accept_3_2 7 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 281 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 281 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 281 (accept_3_2 4 194 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 281
  (Polychromatic418967fa.accept_17_2_7_9_1_2796 2 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 281 (accept_3_2 1 194 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 193 281
  (Eq.refl Bool.true) (allA_of_3_0 89 193 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 192 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 192 281 (accept_3_2 88 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 192 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 192 281 (accept_3_2 85 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 192 281 (Polychromatic418967fa.accept_19_8_2_15_1_2426 84 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 192 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 83 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 192 281 (accept_3_2 82 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 192 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 192 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 192 281 (accept_3_2 79 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 192 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 192 281 (accept_3_2 76 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 192 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 192 281 (accept_3_2 73 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 192 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 192 281 (accept_3_2 70 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 192 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 192 281 (accept_3_2 67 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 192 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 281 (accept_3_2 64 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 192 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 192 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 192 281 (accept_3_2 61 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 192 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 192 281 (accept_3_2 58 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 192 281 (Polychromatic418967fa.accept_13_5_10_8_1_1127 57 192 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 192 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 56 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 192 281 (accept_3_2 55 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 281 (accept_3_2 52 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 192 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 192 281 (accept_3_2 49 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 192 281 (Polychromatic418967fa.accept_17_14_5_9_1_7766 48 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 192 281 (accept_3_2 46 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 192 281 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 192 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 192 281 (accept_3_2 43 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 192 281 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 281 (accept_3_2 40 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 281
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 192 281 (accept_3_2 37 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 192 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 192 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 192 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 281 (accept_3_2 34 192 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424
  33 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 281 (accept_3_2 31 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 281 (accept_3_2 28 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 281 (Polychromatic418967fa.accept_18_9_12_11_1_5642 27 192
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 192 281 (accept_3_2 25 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 281 (accept_3_2 22 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 281 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 192 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 281
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 281 (accept_3_2 19 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 281 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 281 (accept_3_2 16 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 192 281 (accept_3_2 13 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 281 (accept_3_2 10 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 281 (accept_3_2 7 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  192 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 192 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 281 (accept_3_2 4 192 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 281 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 192 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 281 (accept_3_2 1 192 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 191 281
  (Eq.refl Bool.true) (allA_succ_of_accept 90 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 191 281
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 89 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 191 281 (accept_3_2 88 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 191 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 191 281 (accept_3_2 85 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 191 281 (Polychromatic418967fa.accept_19_8_1_15_1_2496 84 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 191 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 191 281 (accept_3_2 82 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 191 281 (Polychromatic418967fa.accept_13_3_9_8_1_4202 81 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 191 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 191 281 (accept_3_2 79 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 191 281
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 77 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 191 281 (accept_3_2 76 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 191 281 (Polychromatic418967fa.accept_23_6_7_5_1_15708 75 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 191 281 (accept_3_2 73 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 191 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 72 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 191 281
  (Polychromatic418967fa.accept_19_14_1_15_1_7914 71 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 191 281 (accept_3_2 70 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 191 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 191 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 191 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 68 191
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 281 (accept_3_2 67 191
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2
  66 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 281
  (Polychromatic418967fa.accept_17_14_4_9_1_2792 65 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 281 (accept_3_2 64 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 281 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 281 (accept_3_2 61 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 281 (Polychromatic418967fa.accept_22_16_15_17_1_17274 60 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 281 (accept_3_2 58 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 281 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 281 (Polychromatic418967fa.accept_13_4_9_8_1_1736 56 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 281 (accept_3_2 55 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 281
  (Polychromatic418967fa.accept_13_1_9_8_1_1734 53 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 191 281 (accept_3_2 52 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 191 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 281 (accept_3_2 49 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 281
  (Polychromatic418967fa.accept_17_13_4_9_1_6390 47 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 281 (accept_3_2 46 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 281 (Polychromatic418967fa.accept_20_4_11_1_1_10409 44 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 281 (accept_3_2 43 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 281
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 281 (accept_3_2 40 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 281 (Polychromatic418967fa.accept_25_14_16_6_1_17273 39 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 281 (accept_3_2 37 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 281 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 191
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 281
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 281 (accept_3_2 34 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 281 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 281 (Polychromatic418967fa.accept_20_12_11_1_1_3032 32 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 281 (accept_3_2 31 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 281
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 29 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 281 (accept_3_2 28 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 281 (accept_3_2 25 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 281
  (Polychromatic418967fa.accept_19_4_1_15_1_6415 23 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 281 (accept_3_2 22 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 281 (Polychromatic418967fa.accept_19_2_1_15_1_2494 21 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 281 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 281 (accept_3_2 19 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 281
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 281 (accept_3_2 16 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 281 (Polychromatic418967fa.accept_21_15_2_8_1_14291 15 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 281 (accept_3_2 13 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 281 (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 191 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 281
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 281 (accept_3_2 10 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 281 (Polychromatic418967fa.accept_23_9_7_5_1_12541 9 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 281 (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 281 (accept_3_2 7 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 281
  (Polychromatic418967fa.accept_19_5_1_15_1_9264 5 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 281 (accept_3_2 4 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 281 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 191 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 281 (accept_3_2 1 191 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 190 281
  (Eq.refl Bool.true) (allA_of_3_0 92 190 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 189 281 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 189 281 (accept_3_2 91 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 189 281 (Polychromatic418967fa.accept_13_12_7_8_1_1104 90 189 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 189 281
  (Polychromatic418967fa.accept_17_4_2_9_1_3896 89 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 189 281 (accept_3_2 88 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 87 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 189 281 (accept_3_2 85 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 189 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 189 281
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 83 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 189 281 (accept_3_2 82 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 189 281 (Polychromatic418967fa.accept_11_4_2_6_1_389 81 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 189 281 (accept_3_2 79 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 189 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 78 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 189 281
  (Polychromatic418967fa.accept_13_12_7_8_1_1104 77 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 189 281 (accept_3_2 76 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 189 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 189 281 (accept_3_2 73 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 189 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 189 281
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 71 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 189 281 (accept_3_2 70 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 189 281 (Polychromatic418967fa.accept_14_13_7_1_1_1618 69 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 189 281 (accept_3_2 67 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 189 281 (Polychromatic418967fa.accept_13_1_7_8_1_1796 66 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 189 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 189 281 (accept_3_2 64 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 189 281 (accept_3_2 61 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 189 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 189 281
  (Polychromatic418967fa.accept_11_4_2_6_1_389 59 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 189 281 (accept_3_2 58 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 189 281 (Polychromatic418967fa.accept_26_5_7_21_1_6064 57 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 189 281 (accept_3_2 55 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 189 281 (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 189 281
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 53 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 189 281 (accept_3_2 52 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 281 (accept_3_2 49 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 281
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 281 (accept_3_2 46 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 281 (accept_3_2 43 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 281 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 281
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 281 (accept_3_2 40 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 281 (accept_3_2 37 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 281 (accept_3_2 34 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 281 (Polychromatic418967fa.accept_16_1_13_9_1_2551 33 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 281 (accept_3_2 31 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 281 (Polychromatic418967fa.accept_18_12_9_11_1_4370 30 189 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 281
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 281 (accept_3_2 28 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 281 (accept_3_2 25 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 281 (Polychromatic418967fa.accept_17_7_2_9_1_6396 24 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 281
  (Polychromatic418967fa.accept_13_10_7_8_1_1794 23 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 281 (accept_3_2 22 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 281 (Polychromatic418967fa.accept_15_6_9_11_1_858 21 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 281 (accept_3_2 19 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 281 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 281
  (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 281 (accept_3_2 16 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 281 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 281 (accept_3_2 13 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 281 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 281
  (Polychromatic418967fa.accept_17_11_2_9_1_6358 11 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 281 (accept_3_2 10 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 281 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 281 (accept_3_2 7 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 281 (Polychromatic418967fa.accept_14_6_7_1_1_78 6 189 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 281
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 281 (accept_3_2 4 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 281 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 189 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 281 (accept_3_2 1 189 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 188
  281 (Eq.refl Bool.true) (allA_succ_of_accept 93 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 188 281
  (Polychromatic418967fa.accept_13_1_6_8_1_208 92 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 188 281 (accept_3_2 91 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 188 281 (Polychromatic418967fa.accept_19_14_17_15_1_3761 90 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 188 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 188 281 (accept_3_2 88 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 188 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 188 281 (accept_3_2 85 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 188 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 188 281 (Polychromatic418967fa.accept_10_3_8_1_1_182 83 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 188 281 (accept_3_2 82 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 188 281
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 80 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 188 281 (accept_3_2 79 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 188 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 188 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 188 281 (accept_3_2 76 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 188 281
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 188 281 (accept_3_2 73 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 188 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 188 281 (Polychromatic418967fa.accept_11_5_1_6_1_774 71 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 188 281 (accept_3_2 70 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 188 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 188 281 (accept_3_2 67 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 188 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 188 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 188 281 (accept_3_2 64 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 188 281
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 62 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 188 281 (accept_3_2 61 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 188 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 188 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 188 281 (accept_3_2 58 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 188 281
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 56 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 188 281 (accept_3_2 55 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 188 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 188 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 188 281 (accept_3_2 52 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 188 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 188 281 (accept_3_2 49 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 188 281 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 188 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 188 281 (accept_3_2 46 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 188 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 188 281 (accept_3_2 43 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 188 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 188 281 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 188 281 (accept_3_2 40 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 188 281
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 188 281 (accept_3_2 37 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 188 281 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 188 281 (Polychromatic418967fa.accept_14_7_6_1_1_1656 35 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 188 281 (accept_3_2 34 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 188 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 188 281 (accept_3_2 31 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 188 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 188 281 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 281 (accept_3_2 28 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 188 281
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 188 281 (accept_3_2 25 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 188 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 188 281 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 281 (accept_3_2 22 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 281
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 20 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 188 281 (accept_3_2 19 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 188 281 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 188 281 (Polychromatic418967fa.accept_21_17_20_8_1_9938 17 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 281 (accept_3_2 16 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 281
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 188 281 (accept_3_2 13 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 188 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 281 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 281 (accept_3_2 10 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 281
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 8 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 281 (accept_3_2 7 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 281 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 281 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 281 (accept_3_2 4 188 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 281
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 281 (accept_3_2 1 188 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 187
  281 (Eq.refl Bool.true) (allA_of_3_0 95 187 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 186 281
  (Eq.refl Bool.true) (allA_succ_of_accept 95 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 186 281 (accept_3_2 94 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 186 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 186 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 186 281 (accept_3_2 91 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 186 281 (Polychromatic418967fa.accept_13_12_4_8_1_1120 90 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 186 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 186 281 (accept_3_2 88 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 186 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 86 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 186 281 (accept_3_2 85 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 186 281 (accept_3_2 82 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 186 281 (Polychromatic418967fa.accept_14_11_4_1_1_4255 81 186 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 186 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 80 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 186 281 (accept_3_2 79 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 186 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 186 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 186 281 (accept_3_2 76 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 186 281
  (Polychromatic418967fa.accept_13_9_4_8_1_1752 74 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 186 281 (accept_3_2 73 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 186 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 186 281 (accept_3_2 70 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 186 281 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 186 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 186 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 186 281 (accept_3_2 67 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 186 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 186 281 (Polychromatic418967fa.accept_10_5_6_1_1_836 65 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 186 281 (accept_3_2 64 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 186 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 186 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 186 281 (accept_3_2 61 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 186 281 (Polychromatic418967fa.accept_11_5_10_6_1_793 60 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 186 281 (accept_3_2 58 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 186 281
  (Polychromatic418967fa.accept_20_16_6_1_1_7270 56 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 186 281 (accept_3_2 55 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 186 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 186 281 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 186 281 (accept_3_2 52 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 186 281 (accept_3_2 49 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 281 (accept_3_2 46 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 186 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 186 281 (accept_3_2 43 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 186 281 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 186 281 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 281 (accept_3_2 40 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 281
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 186 281 (accept_3_2 37 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 186 281 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 281 (accept_3_2 34 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 186 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 186 281 (accept_3_2 31 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 186 281 (Polychromatic418967fa.accept_22_7_10_17_1_7956 29 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 281 (accept_3_2 28 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 281
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 281 (accept_3_2 25 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 186 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 281 (accept_3_2 22 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 281 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 281
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 281 (accept_3_2 19 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 281 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 281 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 281 (accept_3_2 16 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 281
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 281 (accept_3_2 13 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 186 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 281 (accept_3_2 10 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 281 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 281
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 281 (accept_3_2 7 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 281 (Polychromatic418967fa.accept_17_6_16_9_1_5129 6 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 281 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 281 (accept_3_2 4 186 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 281
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 281 (accept_3_2 1 186 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  281)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 185
  281 (Eq.refl Bool.true) (allA_succ_of_accept 96 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 185 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 185 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 95 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 185 281 (accept_3_2 94 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 185 281 (Polychromatic418967fa.accept_15_2_5_11_1_1563 92 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 185 281 (accept_3_2 91 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 185 281 (Polychromatic418967fa.accept_20_10_5_1_1_4406 90 185
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 185 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 185 281 (accept_3_2 88 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 87 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 185 281 (accept_3_2 85 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 185 281
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 83 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 185 281 (accept_3_2 82 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 185 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 185 281 (accept_3_2 79 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 185 281
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 185 281 (accept_3_2 76 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 185 281 (accept_3_2 73 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 185 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 185 281 (accept_3_2 70 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 69 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 185 281 (accept_3_2 67 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 185 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 185 281 (accept_3_2 64 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 185 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 185 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 185 281 (accept_3_2 61 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 185 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 185 281 (accept_3_2 58 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 185 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 185 281 (accept_3_2 55 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 185 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 185 281 (accept_3_2 52 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 185 281 (Polychromatic418967fa.accept_13_11_3_8_1_1786 50 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 185 281 (accept_3_2 49 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 185 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 185 281 (accept_3_2 46 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 185 281 (Polychromatic418967fa.accept_19_7_14_15_1_2477 45 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 281 (accept_3_2 43 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 281
  (Polychromatic418967fa.accept_17_7_15_9_1_9019 41 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 185 281 (accept_3_2 40 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 281 (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 281 (accept_3_2 37 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 281 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 185
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 281 (accept_3_2 34 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 281 (accept_3_2 31 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 281
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 281 (accept_3_2 28 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 281 (Polychromatic418967fa.accept_23_4_1_5_1_7401 27 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 281 (accept_3_2 25 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 281
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 281 (accept_3_2 22 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 281 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 281 (accept_3_2 19 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 281 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 185 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 281
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 281 (accept_3_2 16 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 281 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 281 (accept_3_2 13 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 281 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 281
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 281 (accept_3_2 10 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 281 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 281 (accept_3_2 7 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 281 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 185 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 281
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 281 (accept_3_2 4 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 281 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 185 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 281 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 281 (accept_3_2 1 185 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  184 281 (Eq.refl Bool.true) (allA_of_3_0 98 184 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 183 281
  (Eq.refl Bool.true) (allA_succ_of_accept 98 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 183 281 (accept_3_2 97 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 183 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 95 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 183 281 (accept_3_2 94 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 183 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 183 281 (accept_3_2 91 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 183 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 89 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 183 281 (accept_3_2 88 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 183 281 (accept_3_2 85 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 183 281 (Polychromatic418967fa.accept_13_6_1_8_1_1116 84 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 183 281
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 83 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 183 281 (accept_3_2 82 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 183 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 183 281 (accept_3_2 79 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 77 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 183 281 (accept_3_2 76 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 183 281 (Polychromatic418967fa.accept_19_18_12_15_1_9288 75 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 183 281 (accept_3_2 73 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 183 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 183
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 183 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 71 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 183 281 (accept_3_2 70 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 183 281 (accept_3_2 67 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 183 281
  (Polychromatic418967fa.accept_19_8_12_15_1_3703 65 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 183 281 (accept_3_2 64 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 183 281 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 183 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 183 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 183 281 (accept_3_2 61 183 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431
  60 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 59 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 183 281 (accept_3_2 58 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 183 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 183 281 (accept_3_2 55 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 183 281 (accept_3_2 52 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 281 (accept_3_2 49 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 281 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 281
  (Polychromatic418967fa.accept_21_5_15_8_1_9935 47 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 281 (accept_3_2 46 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 183 281 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 281 (accept_3_2 43 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 281 (accept_3_2 40 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 281 (Polychromatic418967fa.accept_17_5_13_9_1_9018 39 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 281 (accept_3_2 37 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 281 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 281 (accept_3_2 34 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 281 (accept_3_2 31 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 281
  (Polychromatic418967fa.accept_15_14_3_11_1_850 29 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 281 (accept_3_2 28 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 281 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 281 (accept_3_2 25 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 281 (accept_3_2 22 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 281 (accept_3_2 19 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 281
  (Polychromatic418967fa.accept_9_8_3_2_1_417 17 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 281 (accept_3_2 16 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 281 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 281 (accept_3_2 13 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 281 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 281
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 281 (accept_3_2 10 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 281 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 281 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 281 (accept_3_2 7 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 281
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 281 (accept_3_2 4 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 281 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3 183 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 281 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 281 (accept_3_2 1 183 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  182 281 (Eq.refl Bool.true) (allA_succ_of_accept 99 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 182 281
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 98 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 182 281 (accept_3_2 97 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 182 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 96 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 182 281 (accept_3_2 94 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 182 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 92 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 182 281 (accept_3_2 91 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 182 281 (Polychromatic418967fa.accept_17_5_12_9_1_10091 90 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 182 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 89 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 182 281 (accept_3_2 88 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 182 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 86 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 182 281 (accept_3_2 85 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 182 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 84 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 182 281 (accept_3_2 82 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 182 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 80 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 182 281 (accept_3_2 79 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 182 281 (Polychromatic418967fa.accept_19_2_11_15_1_2404 78 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 182 281 (Polychromatic418967fa.accept_16_13_6_9_1_2561 77 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 182 281 (accept_3_2 76 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 182 281
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 74 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 182 281 (accept_3_2 73 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 182 281 (Polychromatic418967fa.accept_17_4_12_9_1_6379 72 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 182 281 (accept_3_2 70 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 69
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 182 281
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 182 281 (accept_3_2 67 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 182 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 66 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 182 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 182 281 (accept_3_2 64 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 182 281
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 182 281
  (Polychromatic418967fa.accept_19_5_11_15_1_2460 62 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 182 281 (accept_3_2 61 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 182 281 (Polychromatic418967fa.accept_25_10_7_6_1_17272 60 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 59
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 182 281 (accept_3_2 58
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 182 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 57 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 182 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 182 281 (accept_3_2 55 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 182 281 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 182 281
  (Polychromatic418967fa.accept_10_3_2_1_1_839 53 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 182 281 (accept_3_2 52 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 182 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596 50 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 182 281 (accept_3_2 49 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 182 281 (Polychromatic418967fa.accept_17_14_12_9_1_2774 48 182
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 182 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 182 281 (accept_3_2 46 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 182 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 182 281 (accept_3_2 43 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 182 281 (Polychromatic418967fa.accept_19_4_11_15_1_3743 42 182
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 182 281
  (Polychromatic418967fa.accept_22_19_6_17_1_17271 41 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 182 281 (accept_3_2 40 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 281 (Polychromatic418967fa.accept_17_4_12_9_1_6379 38 182
  281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 182 281 (accept_3_2 37 182
  281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 182 281
  (Polychromatic418967fa.accept_10_6_2_1_1_494 36 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 281 (accept_3_2 34 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 182 281 (accept_3_2 31
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 182 281
  (Polychromatic418967fa.accept_22_8_6_17_1_9593 30 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 182 281 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 281 (accept_3_2 28 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 281 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 281 (accept_3_2 25
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 281
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 24 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 281 (accept_3_2 22 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 182 281 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 281 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 281 (accept_3_2 19
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 281
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 182 281 (Polychromatic418967fa.accept_18_17_2_11_1_9749 17 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 281 (accept_3_2 16 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 281 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 281
  (Polychromatic418967fa.accept_17_14_12_9_1_2774 14 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 182 281 (accept_3_2 13 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 182 281 (Polychromatic418967fa.accept_21_12_14_8_1_5258 12 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 281 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 281 (accept_3_2 10
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 281
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 182 281 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 281 (accept_3_2 7 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 182 281 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 182 281 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 281 (Polychromatic418967fa.accept_15_5_2_11_1_1596
  5 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 281 (accept_3_2 4
  182 281 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 281
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 281 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 182 281 (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 281 (accept_3_2 1 182 281 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 182
  281))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_281_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


