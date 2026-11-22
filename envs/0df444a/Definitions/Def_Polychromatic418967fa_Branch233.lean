-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch233
-- name    : Polychromatic418967fa_Branch233
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:34.146531+00:00
-- url     : https://prove2.me/theorems/46d7fd45-b5f6-4261-b21d-e90fcf8ed491
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch233_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_233 : allB 233 233 :=
  allB_succ' 2 232 233 (Eq.refl Bool.true) (allA_of_3_0 2 232 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  231 233 (Eq.refl Bool.true) (allA_succ_of_accept 2 231 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 233 (accept_3_2 1 231 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 233))) (allB_succ' 4 230 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 230 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 230 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 233 (accept_3_2 1 230 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230 233)))) (allB_succ' 5 229 233 (Eq.refl Bool.true) (allA_of_3_0
  5 229 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 228 233 (Eq.refl Bool.true) (allA_succ_of_accept 5
  228 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 228 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 228 233 (accept_3_2 4 228 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 228 233 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 228 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 228 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 233 (accept_3_2 1 228 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 233)))))) (allB_succ' 7 227 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 227 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 227 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 233 (accept_3_2 4 227 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  227 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 233 (accept_3_2 1 227 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227 233)))))))
  (allB_succ' 8 226 233 (Eq.refl Bool.true) (allA_of_3_0 8 226 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 225 233 (Eq.refl Bool.true) (allA_succ_of_accept 8 225 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 233 (accept_3_2 7 225 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  225 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 233
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 225 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 233 (accept_3_2 4 225 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 225 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 225 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 233 (accept_3_2 1 225 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 225 233))))))))) (allB_succ' 10 224 233 (Eq.refl Bool.true) (allA_succ_of_accept 9 224
  233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 224 233 (Polychromatic418967fa.accept_17_8_3_12_1_5354 8 224 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 233 (accept_3_2 7 224 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 224 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 224 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376
  5 224 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 233 (accept_3_2 4
  224 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 224 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 224 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 233 (accept_3_2 1 224 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 224 233)))))))))) (allB_succ' 11 223 233 (Eq.refl Bool.true) (allA_of_3_0 11 223 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 222 233 (Eq.refl Bool.true) (allA_succ_of_accept 11 222 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 233 (accept_3_2 10 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  222 233 (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 222 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 222 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 233 (accept_3_2 7 222 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 233 (Polychromatic418967fa.accept_17_6_1_12_1_4115 6 222 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 233 (accept_3_2 4 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  222 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 222 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 222 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 233 (accept_3_2 1 222 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 222 233)))))))))))) (allB_succ' 13 221 233 (Eq.refl Bool.true) (allA_succ_of_accept 12
  221 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 221 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 233 (accept_3_2 10 221 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 233 (Polychromatic418967fa.accept_19_9_12_5_1_5695 9 221 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 233
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 233 (accept_3_2 7 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 221 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 233 (accept_3_2 4 221 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 221 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 233 (accept_3_2 1 221 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  233))))))))))))) (allB_succ' 14 220 233 (Eq.refl Bool.true) (allA_of_3_0 14 220 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 219 233 (Eq.refl Bool.true) (allA_succ_of_accept 14 219 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 233 (accept_3_2 13 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 219 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 233 (accept_3_2 10 219 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 219 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 233 (accept_3_2 7 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 219 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 233 (accept_3_2 4 219 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 3 219 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 233 (accept_3_2 1 219 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  233))))))))))))))) (allB_succ' 16 218 233 (Eq.refl Bool.true) (allA_succ_of_accept 15 218 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 218 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 218 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 233 (accept_3_2 13 218 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 218 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 218 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 233 (accept_3_2 10
  218 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 218 233 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 218 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 233 (accept_3_2 7 218 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 218 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 218 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 233 (accept_3_2 4 218
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 233 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 233
  (Polychromatic418967fa.accept_13_2_10_12_1_757 2 218 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 233 (accept_3_2 1 218 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  233)))))))))))))))) (allB_succ' 17 217 233 (Eq.refl Bool.true) (allA_of_3_0 17 217 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 216 233 (Eq.refl Bool.true) (allA_succ_of_accept 17 216 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 233 (accept_3_2 16 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 216 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 216 233 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 216 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 233 (accept_3_2 13 216 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 233 (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 216
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 233 (accept_3_2 10 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  216 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 216 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 216 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 233 (accept_3_2 7 216 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 233 (Polychromatic418967fa.accept_19_6_7_5_1_256 6 216 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 233
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 233 (accept_3_2 4 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 216 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 233 (Polychromatic418967fa.accept_15_2_6_8_1_754 2 216 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 233 (accept_3_2 1 216 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 233)))))))))))))))))) (allB_succ' 19 215 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 215 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 215 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 233 (accept_3_2 16 215 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 233 (Polychromatic418967fa.accept_11_4_6_2_1_51
  15 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 233 (accept_3_2 13 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 215 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 233 (accept_3_2 10 215 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 233 (Polychromatic418967fa.accept_27_9_26_17_1_980 9 215 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 233
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 233 (accept_3_2 7 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 215 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 233 (accept_3_2 4 215 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 215 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 233 (accept_3_2 1 215 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  233))))))))))))))))))) (allB_succ' 20 214 233 (Eq.refl Bool.true) (allA_of_3_0 20 214 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 213 233 (Eq.refl Bool.true) (allA_succ_of_accept 20 213 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 233 (accept_3_2 19 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 213 233 (Polychromatic418967fa.accept_19_18_4_5_1_5723 18 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 213 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 213 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 233 (accept_3_2 16 213 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 213 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 213 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 233 (accept_3_2 13 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 213 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 213 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 213 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 233 (accept_3_2 10 213 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 213 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 213 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 233 (accept_3_2 7 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  213 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 213 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 213 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 233 (accept_3_2 4 213 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 233 (accept_3_2 1 213 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  233))))))))))))))))))))) (allB_succ' 22 212 233 (Eq.refl Bool.true) (allA_succ_of_accept 21 212 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 212 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 212 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 233 (accept_3_2 19 212 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 212 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 212 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 233
  (Polychromatic418967fa.accept_19_17_3_5_1_3088 17 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 212 233 (accept_3_2 16 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 212 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 212 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 212 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 233 (accept_3_2 13 212 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 212 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 233 (accept_3_2 10 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 212 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 233 (accept_3_2 7 212 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 212 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 233 (accept_3_2 4 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 212 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 233 (accept_3_2 1 212 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 233)))))))))))))))))))))) (allB_succ' 23 211 233 (Eq.refl Bool.true) (allA_of_3_0
  23 211 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 210 233 (Eq.refl Bool.true) (allA_succ_of_accept 23
  210 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 210 233 (accept_3_2 22 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 210 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 210 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 233 (accept_3_2 19 210 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 233
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 210 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 233 (accept_3_2 16 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 210 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 233 (Polychromatic418967fa.accept_9_5_3_8_1_316
  14 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 233 (accept_3_2 13
  210 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 233
  (Polychromatic418967fa.accept_16_12_2_9_1_3461 12 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 210 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 233 (accept_3_2 10 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 210 233 (Polychromatic418967fa.accept_18_9_12_17_1_6060 9 210 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 233
  (Polychromatic418967fa.accept_27_8_21_17_1_13951 8 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 210 233 (accept_3_2 7 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 210 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 210 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 210 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 233 (accept_3_2 4 210 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 233 (accept_3_2 1 210 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  233)))))))))))))))))))))))) (allB_succ' 25 209 233 (Eq.refl Bool.true) (allA_succ_of_accept 24 209 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 209 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 209 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 233 (accept_3_2 22 209 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 209 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 20 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 233 (accept_3_2 19 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 233 (accept_3_2 16 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 209 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 233 (accept_3_2 13 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 233 (accept_3_2 10 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 209 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 233 (accept_3_2 7 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 233 (accept_3_2 4 209 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 209 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 233
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 233 (accept_3_2 1 209 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  233))))))))))))))))))))))))) (allB_succ' 26 208 233 (Eq.refl Bool.true) (allA_of_3_0 26 208 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 207 233 (Eq.refl Bool.true) (allA_succ_of_accept 26 207 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 233 (accept_3_2 25 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 233 (Polychromatic418967fa.accept_22_1_9_13_1_2894 23 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 233 (accept_3_2 22 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 207
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 233 (accept_3_2 19 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 233 (Polychromatic418967fa.accept_28_17_11_9_1_13950 17 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 233 (accept_3_2 16 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 207
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 233 (accept_3_2 13 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 233 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 233 (accept_3_2 10 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 207 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 233 (accept_3_2 7 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 207 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 233 (accept_3_2 4 207 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 207 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 233 (accept_3_2 1 207 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  233))))))))))))))))))))))))))) (allB_succ' 28 206 233 (Eq.refl Bool.true) (allA_succ_of_accept 27 206 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 206 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 206 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 233 (accept_3_2 25 206 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 206 233 (Polychromatic418967fa.accept_17_7_2_12_1_1069 24 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 206 233 (accept_3_2 22 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 206 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 206 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 206 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 233 (accept_3_2 19 206 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 206 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 206 233 (accept_3_2 16 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 206 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 206 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 233 (accept_3_2 13 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 206 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 206 233 (accept_3_2 10 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  206 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 206 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 206 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 233 (accept_3_2 7 206 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 206 233 (accept_3_2 4 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  206 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 206 233 (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 233 (accept_3_2 1 206 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 206 233)))))))))))))))))))))))))))) (allB_succ' 29 205 233 (Eq.refl
  Bool.true) (allA_of_3_0 29 205 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 204 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 204 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 233 (accept_3_2 28 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 204 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 204 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 204 233 (Polychromatic418967fa.accept_11_4_6_2_1_51
  26 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 233 (accept_3_2 25
  204 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 204 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 204 233 (accept_3_2 22 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 204 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 204 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 204 233 (Polychromatic418967fa.accept_7_6_1_2_1_230
  20 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 233 (accept_3_2 19
  204 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 233
  (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 233 (accept_3_2 16 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 204 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 233 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 233 (accept_3_2 13
  204 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 233
  (Polychromatic418967fa.accept_9_3_6_8_1_308 12 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 233 (accept_3_2 10 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 204 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813
  8 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 233 (accept_3_2 7
  204 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 233 (accept_3_2 4 204 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  204 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 233 (accept_3_2 1 204
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 233)))))))))))))))))))))))))))))) (allB_succ' 31 203 233
  (Eq.refl Bool.true) (allA_succ_of_accept 30 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 203 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 233 (accept_3_2 28 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 233 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 233 (accept_3_2 25 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 203 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 233
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 203 233 (accept_3_2 22 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 203 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 203 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 203 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 233 (accept_3_2 19 203 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 233
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 233 (accept_3_2 16 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 233 (accept_3_2 13 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 203 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 203 233 (accept_3_2 10 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  203 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 203 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 233 (accept_3_2 7 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 233
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 233 (accept_3_2 4 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 203 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 233 (accept_3_2 1 203 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 233))))))))))))))))))))))))))))))) (allB_succ' 32 202 233 (Eq.refl Bool.true)
  (allA_of_3_0 32 202 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 201 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 233 (accept_3_2 31 201 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 233 (Polychromatic418967fa.accept_20_10_1_13_1_3848 30 201 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 233 (accept_3_2 28 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 233 (accept_3_2 25 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 201 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 233 (accept_3_2 22 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 233 (Polychromatic418967fa.accept_14_7_5_9_1_2911 21 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 233 (accept_3_2 19 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 201 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 233 (accept_3_2 16 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 233 (accept_3_2 13 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 201 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 233 (accept_3_2 10 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 233 (Polychromatic418967fa.accept_17_9_14_12_1_9177 9 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 233 (accept_3_2 7 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 201 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 233 (accept_3_2 4 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 201 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 233 (accept_3_2 1 201 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 233))))))))))))))))))))))))))))))))) (allB_succ' 34 200 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 200 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 200 233 (accept_3_2 31 200 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 200 233 (Polychromatic418967fa.accept_9_3_2_8_1_108
  30 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 200 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 200 233 (accept_3_2 28 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 200 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 200 233 (accept_3_2 25 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 200 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 200 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 200 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 200 233 (accept_3_2 22 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 200 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 200 233 (accept_3_2 19 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 200 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 200 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 233
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 200 233 (accept_3_2 16 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 200 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 200 233 (accept_3_2 13 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 200 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 200 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 200 233 (accept_3_2 10 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 200 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 200 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 233 (accept_3_2 7 200 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 200 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 200 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 200 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 200 233 (accept_3_2 4 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  200 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 200 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 200 233 (accept_3_2 1 200 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 200 233)))))))))))))))))))))))))))))))))) (allB_succ' 35 199 233 (Eq.refl Bool.true)
  (allA_of_3_0 35 199 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 198 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 198 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 233 (accept_3_2 34 198 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 198 233 (Polychromatic418967fa.accept_17_16_11_12_1_2008 33 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 198 233
  (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 198 233 (accept_3_2 31 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 198 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 30 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 198 233 (Polychromatic418967fa.accept_16_13_6_9_1_2561 29 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 233 (accept_3_2 28 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 198 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 198 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 198 233 (accept_3_2 25 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 198 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 198 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 198 233 (accept_3_2 22 198 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 198 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 233
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 198 233 (accept_3_2 19 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 198 233 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 198 233 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 233 (accept_3_2 16 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 233
  (Polychromatic418967fa.accept_17_14_11_12_1_4109 14 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 198 233 (accept_3_2 13 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 198 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 198 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 233 (accept_3_2 10 198 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025
  9 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 233
  (Polychromatic418967fa.accept_20_8_18_13_1_8326 8 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 198 233 (accept_3_2 7 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  198 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 198 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 5 198 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 233 (accept_3_2 4 198 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 233
  (Polychromatic418967fa.accept_13_2_3_12_1_735 2 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 233 (accept_3_2 1 198 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  233)))))))))))))))))))))))))))))))))))) (allB_succ' 37 197 233 (Eq.refl Bool.true) (allA_succ_of_accept 36 197 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 197 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 35 197 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 233 (accept_3_2 34 197 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 197 233 (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 233
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 32 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 233 (accept_3_2 31 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 233 (Polychromatic418967fa.accept_13_4_2_12_1_2800 30 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 233 (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 233 (accept_3_2 28 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 197 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 233
  (Polychromatic418967fa.accept_10_6_7_3_1_547 26 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 233 (accept_3_2 25 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 233 (accept_3_2 22 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 197
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 233 (accept_3_2 19 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 197 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 233 (accept_3_2 16 197 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 233
  (Polychromatic418967fa.accept_10_4_7_3_1_54 14 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 233 (accept_3_2 13 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 233 (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 233 (accept_3_2 10 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 197 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 233
  (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 233 (accept_3_2 7 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 197 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 233 (accept_3_2 4 197 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 197 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 233
  (Polychromatic418967fa.accept_17_2_10_12_1_7915 2 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 233 (accept_3_2 1 197 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  233))))))))))))))))))))))))))))))))))))) (allB_succ' 38 196 233 (Eq.refl Bool.true) (allA_of_3_0 38 196 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 195 233 (Eq.refl Bool.true) (allA_succ_of_accept 38 195 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 195 233 (accept_3_2 37 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 195 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 195 233 (Polychromatic418967fa.accept_21_14_6_2_1_4793 35 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 233 (accept_3_2 34 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 195 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 195
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 195 233 (accept_3_2 31 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 195 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 195 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 195 233 (accept_3_2 28 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 233 (accept_3_2 25 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 195 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 195 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 233 (accept_3_2 22 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 233 (accept_3_2 19 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 233 (accept_3_2 16 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 233 (accept_3_2 13 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 233 (accept_3_2 10 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 233 (accept_3_2 7 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 233 (accept_3_2 4 195 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 233 (accept_3_2 1 195 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  233))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 194 233 (Eq.refl Bool.true) (allA_succ_of_accept 39 194 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 194 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 194 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 194 233 (accept_3_2 37 194 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 194 233 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 194 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 194 233 (accept_3_2 34 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 194 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 194 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 194 233 (accept_3_2 31 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 194 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 194 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 194 233 (accept_3_2 28 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 194 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 194 233 (Polychromatic418967fa.accept_27_26_5_17_1_13949 26 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 194 233 (accept_3_2 25 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 194 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 194 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 194 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 194 233 (accept_3_2 22 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 194 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 194 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 233 (accept_3_2 19 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 194 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 194 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 194 233 (accept_3_2 16 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 194 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 194 233 (Polychromatic418967fa.accept_22_14_18_13_1_10864 14 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 233 (accept_3_2 13 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 194 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 233 (accept_3_2 10 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 233 (Polychromatic418967fa.accept_12_8_2_5_1_844 8 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 233 (accept_3_2 7 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 194 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 5 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 233 (accept_3_2 4 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 233 (accept_3_2 1 194 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 233)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 193 233 (Eq.refl
  Bool.true) (allA_of_3_0 41 193 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 192 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 192 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 192 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 233 (accept_3_2 40 192 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 192 233 (Polychromatic418967fa.accept_20_19_12_13_1_2602 39 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 192 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 233 (accept_3_2 37 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 192 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 192 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 192 233 (accept_3_2 34 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 192 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 192 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 192 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 192 233 (accept_3_2 31 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 192 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 192 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 233 (accept_3_2 28 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 192 233 (accept_3_2 25 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 192 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 192 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 233 (accept_3_2 22 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 233 (accept_3_2 19 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 192 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 18 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 233 (Polychromatic418967fa.accept_19_17_2_5_1_7085 17 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 233 (accept_3_2 16 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 192 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 192 233 (accept_3_2 13 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 192 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 192 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 233 (accept_3_2 10 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 233 (accept_3_2 7 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  192 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 192 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 233 (accept_3_2 4 192 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 192 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 233 (accept_3_2 1 192 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  233)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 191 233 (Eq.refl Bool.true) (allA_succ_of_accept 42 191
  233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 191 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 191 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 191 233 (accept_3_2 40 191 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 191 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 191 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 191 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 233 (accept_3_2 37
  191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 233
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 191 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 191 233 (accept_3_2 34 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 191 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 191 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 191 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 191 233 (accept_3_2 31 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 191 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 191 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 233 (accept_3_2 28 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 191
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 233 (accept_3_2 25 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 233 (accept_3_2 22 191 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 233
  (Polychromatic418967fa.accept_11_9_4_2_1_600 20 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 233 (accept_3_2 19 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 233 (accept_3_2 16 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 191 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 233 (accept_3_2 13 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 233 (Polychromatic418967fa.accept_24_11_23_17_1_7012 11 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 233 (accept_3_2 10 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 191 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 233
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 233 (accept_3_2 7 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 233 (accept_3_2 4 191 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 191 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 233 (accept_3_2 1 191 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  233))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 190 233 (Eq.refl Bool.true) (allA_of_3_0 44 190 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 189 233 (Eq.refl Bool.true) (allA_succ_of_accept 44 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 189 233 (accept_3_2 43 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 189 233 (Polychromatic418967fa.accept_19_4_18_5_1_929 42 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 189 233 (Polychromatic418967fa.accept_17_7_2_12_1_1069 41 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 189 233 (accept_3_2 40 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 189 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 189 233 (accept_3_2 37 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 189 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 189 233 (Polychromatic418967fa.accept_28_7_21_9_1_13948 35 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 189 233 (accept_3_2 34 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 233 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 189 233 (accept_3_2 31 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 189 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 189 233 (Polychromatic418967fa.accept_15_14_9_8_1_3165 29 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 233 (accept_3_2 28 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 233 (accept_3_2 25 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 189 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 233 (accept_3_2 22 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 233 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 233 (accept_3_2 19 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 233 (accept_3_2 16 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 233 (accept_3_2 13 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 233 (accept_3_2 10 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 233 (Polychromatic418967fa.accept_19_9_18_5_1_7101 9 189
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 233 (accept_3_2 7 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 233 (accept_3_2 4 189 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 189 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 233 (accept_3_2 1 189 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  233))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 188 233 (Eq.refl Bool.true) (allA_succ_of_accept 45
  188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 188 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 188 233 (accept_3_2 43 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 188 233 (Polychromatic418967fa.accept_23_19_4_3_1_10740 42 188
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 188 233
  (Polychromatic418967fa.accept_10_1_8_3_1_947 41 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 188 233 (accept_3_2 40 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 188 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 188 233 (accept_3_2 37 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 188 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 188 233
  (Polychromatic418967fa.accept_10_5_8_3_1_229 35 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 188 233 (accept_3_2 34 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 188 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 188 233 (accept_3_2 31 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 188 233 (Polychromatic418967fa.accept_17_13_1_12_1_7893 30 188 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 188 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 188 233 (accept_3_2 28 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 188 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 233 (accept_3_2 25 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 188 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 188 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 233
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 188 233 (accept_3_2 22 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 188 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 188
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 233 (accept_3_2 19 188
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 188 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 188 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 233 (accept_3_2 16 188 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 188 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063
  14 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 233 (accept_3_2 13
  188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 233
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 12 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 188 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 233 (accept_3_2 10 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 233 (accept_3_2 7 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 233 (accept_3_2 4 188 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 233 (accept_3_2 1 188 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  233)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 187 233 (Eq.refl Bool.true) (allA_of_3_0 47 187 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 186 233 (Eq.refl Bool.true) (allA_succ_of_accept 47 186 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 186 233 (accept_3_2 46 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 186 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 186 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 186 233 (accept_3_2 43 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 186 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 186
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 186 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 186 233 (accept_3_2 40 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 186 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 186 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 186 233 (accept_3_2 37 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 233 (Polychromatic418967fa.accept_19_17_15_5_1_7096 36 186 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 186 233 (accept_3_2 34 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 186 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 186 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 186 233 (accept_3_2 31 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 186 233 (accept_3_2 28 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 186 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 186 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 186 233 (accept_3_2 25 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 186 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 186 233 (accept_3_2 22 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 186 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 186 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 186 233 (accept_3_2 19 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 233 (accept_3_2 16 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 186 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 186 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 233 (accept_3_2 13 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 186 233 (accept_3_2 10 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  186 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 186 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 233 (accept_3_2 7 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 186 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 233 (accept_3_2 4 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  186 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 186 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 233 (accept_3_2 1 186 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 186 233)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 185 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 185 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 185 233 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 233 (accept_3_2 46
  185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 233
  (Polychromatic418967fa.accept_21_3_17_2_1_11043 45 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 185 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 185 233 (accept_3_2 43 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 185 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 185 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 185 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 185 233 (accept_3_2 40 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 185 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 185 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 185 233 (accept_3_2 37 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 185 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 233
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 185 233 (accept_3_2 34 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 185 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 185 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 185 233 (accept_3_2 31 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 185 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 185 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 185 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 233 (accept_3_2 28 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 233 (accept_3_2 25 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 233
  (Polychromatic418967fa.accept_22_1_9_13_1_2894 23 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 185 233 (accept_3_2 22 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 185 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 185 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 233 (accept_3_2 19 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 233 (accept_3_2 16 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 233 (accept_3_2 13 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 233 (accept_3_2 10 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 233 (accept_3_2 7 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 185 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 233 (accept_3_2 4 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 185 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 233 (accept_3_2 1 185 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 233))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 184 233
  (Eq.refl Bool.true) (allA_of_3_0 50 184 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 183 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 183 233 (accept_3_2 49 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 183 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 183 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 183 233 (accept_3_2 46 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 183 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 183 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 183 233 (accept_3_2 43 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 183 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 183 233 (accept_3_2 40 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 183 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 39 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 233 (accept_3_2 37 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 233 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 233
  (Polychromatic418967fa.accept_15_5_3_8_1_748 35 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 233 (accept_3_2 34 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 233 (accept_3_2 31 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 233 (accept_3_2 28 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 233 (accept_3_2 25 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 233 (accept_3_2 22 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 233 (accept_3_2 19 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 233 (accept_3_2 16 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 233 (accept_3_2 13 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 183 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 233 (accept_3_2 10 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 233 (accept_3_2 7 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 233 (accept_3_2 4 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 233 (accept_3_2 1 183 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 233))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 182 233
  (Eq.refl Bool.true) (allA_succ_of_accept 51 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 182 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 182 233 (accept_3_2 49 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 182 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 233 (accept_3_2 46 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 233 (accept_3_2 43 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 182 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 182 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 182 233 (accept_3_2 40 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 233
  (Polychromatic418967fa.accept_20_18_2_13_1_5265 38 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 182 233 (accept_3_2 37 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 182 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 182 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 182 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 233 (accept_3_2 34 182 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 233 (accept_3_2 31 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 182 233 (Polychromatic418967fa.accept_16_13_6_9_1_2561 29 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 233 (accept_3_2 28 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 233
  (Polychromatic418967fa.accept_11_4_6_2_1_51 26 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 182 233 (accept_3_2 25 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 182 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 233 (accept_3_2 22 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 182 233 (accept_3_2 19 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 233 (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 233 (Polychromatic418967fa.accept_19_17_11_5_1_7092 17 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 233 (accept_3_2 16 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 233 (accept_3_2 13 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 233 (accept_3_2 10 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 233 (accept_3_2 7 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 233 (accept_3_2 4 182 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 233
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 233 (accept_3_2 1 182 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  233)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 181 233 (Eq.refl Bool.true) (allA_of_3_0 53 181
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 180 233 (Eq.refl Bool.true) (allA_succ_of_accept 53 180
  233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 180 233 (accept_3_2 52 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 180 233 (Polychromatic418967fa.accept_19_13_9_5_1_8541 51 180 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 180 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 50 180
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 180 233 (accept_3_2 49 180
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 180 233
  (Polychromatic418967fa.accept_21_6_12_2_1_4801 48 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 180 233 (Polychromatic418967fa.accept_22_3_4_13_1_13947 47 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 180 233 (accept_3_2 46 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 180 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 180 233
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 44 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 180 233 (accept_3_2 43 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 180 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 42 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 180 233 (Polychromatic418967fa.accept_22_19_4_13_1_13946 41 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 233 (accept_3_2 40 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 180 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 180 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 180 233 (accept_3_2 37 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 180 233 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 233 (Polychromatic418967fa.accept_14_7_12_9_1_2926 35 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 180 233 (accept_3_2 34 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 180 233
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 180 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 233 (accept_3_2 31 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 30 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 180 233 (accept_3_2 28 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 180 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 180 233 (Polychromatic418967fa.accept_19_7_9_5_1_8590 26 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 233 (accept_3_2 25 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 233
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 180 233 (accept_3_2 22 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 180 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 180 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 20 180
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 233 (accept_3_2 19 180
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 233 (accept_3_2 16 180 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 233 (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 233
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 180 233 (accept_3_2 13 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 180 233 (Polychromatic418967fa.accept_16_12_4_9_1_4633 12 180 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 233 (accept_3_2 10 180 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9
  180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 233
  (Polychromatic418967fa.accept_16_8_4_9_1_4666 8 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 233 (accept_3_2 7 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  180 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 180 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 233 (accept_3_2 4 180 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 233
  (Polychromatic418967fa.accept_17_2_10_12_1_7915 2 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 233 (accept_3_2 1 180 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 179 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 233 (Polychromatic418967fa.accept_24_5_11_17_1_7068 53 179
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 233 (accept_3_2 52 179
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 233
  (Polychromatic418967fa.accept_15_6_14_8_1_245 51 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 233 (accept_3_2 49 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 179 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 233 (Polychromatic418967fa.accept_7_5_4_2_1_235
  47 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 233 (accept_3_2 46
  179 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 179 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 44 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 233 (accept_3_2 43 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 233 (Polychromatic418967fa.accept_7_6_4_2_1_236
  41 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 233 (accept_3_2 40
  179 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 233
  (Polychromatic418967fa.accept_15_9_14_8_1_1396 39 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 233 (accept_3_2 37 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 179 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 179 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 233
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 179 233 (accept_3_2 34 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 179 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 179
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 233 (accept_3_2 31 179
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2
  30 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 233
  (Polychromatic418967fa.accept_19_10_8_5_1_5689 29 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 179 233 (accept_3_2 28 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 179 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 233 (accept_3_2 25 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 179 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 233 (accept_3_2 22 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 233 (accept_3_2 19 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 233
  (Polychromatic418967fa.accept_21_17_11_2_1_7953 17 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 179 233 (accept_3_2 16 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 179 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 233 (accept_3_2 13 179 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 233 (Polychromatic418967fa.accept_7_5_4_2_1_235
  12 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 233
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 233 (accept_3_2 10 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 179 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 179
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 233 (accept_3_2 7 179 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 233 (accept_3_2 4 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 233 (Polychromatic418967fa.accept_19_3_8_5_1_1875 3 179 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 233 (accept_3_2 1 179 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 233))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 178 233
  (Eq.refl Bool.true) (allA_of_3_0 56 178 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 177 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 233 (accept_3_2 55 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 233
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 53 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 233 (accept_3_2 52 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 177 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 233 (accept_3_2 49 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 233 (accept_3_2 46 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 233 (accept_3_2 43 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 233 (Polychromatic418967fa.accept_16_10_1_9_1_4622 42 177 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 233 (accept_3_2 40 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 233 (accept_3_2 37 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 233 (accept_3_2 34 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 233 (accept_3_2 31 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 233 (accept_3_2 28 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 233 (accept_3_2 25 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 233 (accept_3_2 22 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 233 (accept_3_2 19 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 177 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 233
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 17 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 233 (accept_3_2 16 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 15 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 233 (accept_3_2 13 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 233 (accept_3_2 10 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 233 (accept_3_2 7 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 177 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 233 (accept_3_2 4 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 177 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 233 (accept_3_2 1 177 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 176 233
  (Eq.refl Bool.true) (allA_succ_of_accept 57 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 176 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 176 233 (accept_3_2 55 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 176 233 (Polychromatic418967fa.accept_24_6_8_17_1_13945 54 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 176 233 (Polychromatic418967fa.accept_17_2_6_12_1_7912 53 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 176 233 (accept_3_2 52 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 176 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 176 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 176 233 (accept_3_2 49 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 176 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 176 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 176 233 (accept_3_2 46 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 176 233
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 176 233 (accept_3_2 43 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 176 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 176 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 233 (accept_3_2 40 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 233 (accept_3_2 37 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 36 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 233 (accept_3_2 34 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 233
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 233 (accept_3_2 31 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 233 (accept_3_2 28 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 233 (accept_3_2 25 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 233 (Polychromatic418967fa.accept_13_10_7_12_1_2782 23 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 233 (accept_3_2 22 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 233 (accept_3_2 19 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 233 (accept_3_2 16 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 233 (accept_3_2 13 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 233 (accept_3_2 10 176 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 233 (accept_3_2 7 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 5 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 233 (accept_3_2 4 176 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 233 (accept_3_2 1 176 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 175 233 (Eq.refl Bool.true) (allA_of_3_0
  59 175 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 174 233 (Eq.refl Bool.true) (allA_succ_of_accept 59
  174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 174 233 (accept_3_2 58 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 174 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 174 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 174 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 174 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 233 (accept_3_2 55 174 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 174 233
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 174 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 174 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 233 (accept_3_2 52 174 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 174 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 50
  174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 174 233 (accept_3_2 49
  174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 48 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 174 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 233 (accept_3_2 46 174 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 174 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 174 233
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 44 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 174 233 (accept_3_2 43 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 174 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 174 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 233 (accept_3_2 40 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 174 233 (accept_3_2 37 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 174 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 233 (accept_3_2 34 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 174 233 (accept_3_2 31 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 174 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 174 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 233 (accept_3_2 28 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 233 (accept_3_2 25 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 174 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 233 (accept_3_2 22 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 174 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 233 (accept_3_2 19 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 174 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 174 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 233 (accept_3_2 16 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 174 233 (accept_3_2 13 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 174 233 (Polychromatic418967fa.accept_21_12_6_2_1_7950 12 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 233 (accept_3_2 10 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 233 (accept_3_2 7 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  174 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 174 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 233 (accept_3_2 4 174 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 233 (accept_3_2 1 174 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 173 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 60 173 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 173 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 233 (accept_3_2 58 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 233 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 233
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 56 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 173 233 (accept_3_2 55 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 173 233 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 173 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 233 (accept_3_2 52 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 233 (Polychromatic418967fa.accept_9_6_2_8_1_592
  51 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 233 (accept_3_2 49 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 233 (accept_3_2 46 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 233 (accept_3_2 43 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 233 (accept_3_2 40 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 233 (accept_3_2 37 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 233 (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 233 (accept_3_2 34 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 173 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 233 (accept_3_2 31 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 233 (accept_3_2 28 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 27 173
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 233
  (Polychromatic418967fa.accept_19_7_2_5_1_5680 26 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 233 (accept_3_2 25 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 233 (accept_3_2 22 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 20 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 233 (accept_3_2 19 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 233 (accept_3_2 16 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 233 (accept_3_2 13 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 233 (accept_3_2 10 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 233 (Polychromatic418967fa.accept_23_9_12_3_1_7304 9 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 233
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 8 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 233 (accept_3_2 7 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 233 (accept_3_2 4 173 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 173 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 233
  (Polychromatic418967fa.accept_13_2_4_12_1_745 2 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 233 (accept_3_2 1 173 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 172 233 (Eq.refl Bool.true)
  (allA_of_3_0 62 172 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 171 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 171 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 233 (accept_3_2 61 171 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 171 233 (Polychromatic418967fa.accept_21_18_3_2_1_13928 60 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 233
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 233 (accept_3_2 58 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 171 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 171 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 233 (accept_3_2 55 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 233
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 53 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 233 (accept_3_2 52 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 233 (Polychromatic418967fa.accept_18_15_9_17_1_6043 51 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 233 (accept_3_2 49 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 233 (accept_3_2 46 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 233 (accept_3_2 43 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 233 (accept_3_2 40 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 233 (Polychromatic418967fa.accept_21_18_3_2_1_13928 39 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 233 (accept_3_2 37 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 233
  (Polychromatic418967fa.accept_20_15_11_13_1_11192 35 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 171 233 (accept_3_2 34 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 171 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 171 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 233 (accept_3_2 31 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 233 (accept_3_2 28 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 233 (accept_3_2 25 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 233 (Polychromatic418967fa.accept_20_4_11_13_1_11184 24 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 233
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 233 (accept_3_2 22 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 171 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 171 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 233 (accept_3_2 19 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 233
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 17 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 233 (accept_3_2 16 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 233 (accept_3_2 13 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 233
  (Polychromatic418967fa.accept_22_11_17_13_1_9270 11 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 233 (accept_3_2 10 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 171 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 171 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 233 (accept_3_2 7 171 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 233 (accept_3_2 4 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 233 (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 171 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 233 (accept_3_2 1 171 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  170 233 (Eq.refl Bool.true) (allA_succ_of_accept 63 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 170 233
  (Polychromatic418967fa.accept_20_2_10_13_1_6766 62 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 170 233 (accept_3_2 61 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 170 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 170 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 170 233 (accept_3_2 58 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 170 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57
  170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 170 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 170 233 (accept_3_2 55 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 170 233 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 170 233 (Polychromatic418967fa.accept_14_11_2_9_1_5873 53 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 170 233 (accept_3_2 52 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 170 233
  (Polychromatic418967fa.accept_13_11_1_12_1_742 50 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 170 233 (accept_3_2 49 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 170 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 48 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 170 233 (accept_3_2 46 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 170 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 170 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 170 233 (accept_3_2 43 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 170 233 (Polychromatic418967fa.accept_15_12_5_8_1_5247 42 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 170 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 170 233 (accept_3_2 40 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 233
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 38 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 170 233 (accept_3_2 37 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 170 233 (Polychromatic418967fa.accept_19_17_18_5_1_3012 36 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 233 (accept_3_2 34 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 170 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 170 233 (accept_3_2 31 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 170 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 170 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 233 (accept_3_2 28 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 170 233 (accept_3_2 25 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 170 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 233 (accept_3_2 22 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 170 233 (accept_3_2 19 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 170 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 170 233 (Polychromatic418967fa.accept_16_1_10_9_1_4645 17 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 233 (accept_3_2 16 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 233 (accept_3_2 13 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 233 (Polychromatic418967fa.accept_15_12_5_8_1_5247 12 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 233 (accept_3_2 10 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 233
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 233 (accept_3_2 7 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 233 (Polychromatic418967fa.accept_19_6_18_5_1_5630 6 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 5 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 233 (accept_3_2 4 170 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 233
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 233 (accept_3_2 1 170 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 169 233 (Eq.refl Bool.true)
  (allA_of_3_0 65 169 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 168 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 168 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 168 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 233 (accept_3_2 64 168 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 168 233 (Polychromatic418967fa.accept_16_15_8_9_1_2563 63 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 168 233
  (Polychromatic418967fa.accept_22_18_14_13_1_12531 62 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 168 233 (accept_3_2 61 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 168 233 (Polychromatic418967fa.accept_16_12_8_9_1_2583 60 168 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 168 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 168 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 233 (accept_3_2 58 168 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308
  57 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 168 233 (accept_3_2 55 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 168 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 168 233 (Polychromatic418967fa.accept_29_24_23_1_1_13944 53 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 233 (accept_3_2 52 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 168 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 168
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 50 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 168 233 (accept_3_2 49 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 168 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 233 (accept_3_2 46 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 233
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 168 233 (accept_3_2 43 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 168 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 168 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 233 (accept_3_2 40 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 168 233 (accept_3_2 37 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 168 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 168 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 233 (accept_3_2 34 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 233 (Polychromatic418967fa.accept_16_1_8_9_1_3462 33 168
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 168 233 (accept_3_2 31 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 168 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 233 (accept_3_2 28 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 168 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 168 233 (accept_3_2 25 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 168 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 168 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 233 (accept_3_2 22 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 168 233 (accept_3_2 19 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 168 233 (Polychromatic418967fa.accept_17_1_15_12_1_7907 18 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 233 (Polychromatic418967fa.accept_16_1_8_9_1_3462 17 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 233 (accept_3_2 16 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 168
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 233 (accept_3_2 13 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 168 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 233 (accept_3_2 10 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 233
  (Polychromatic418967fa.accept_19_8_16_5_1_8583 8 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 168 233 (accept_3_2 7 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  168 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 168 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 233 (accept_3_2 4 168 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 233 (accept_3_2 1 168 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 167 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 167 233 (accept_3_2 64 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 167 233
  (Polychromatic418967fa.accept_19_6_15_5_1_5697 63 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 233 (accept_3_2 61 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 167 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 167 233 (accept_3_2 58
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 167 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 167 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 233 (accept_3_2 55 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 233 (Polychromatic418967fa.accept_7_4_6_2_1_451
  53 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 167 233 (accept_3_2 52
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 167 233
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 233 (accept_3_2 49 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 167 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 233 (accept_3_2 46
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 167 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 233 (accept_3_2 43 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 233
  (Polychromatic418967fa.accept_23_18_6_3_1_13943 41 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 233 (accept_3_2 40 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 233 (accept_3_2 37 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 233 (accept_3_2 34 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 233 (accept_3_2 31 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 233 (accept_3_2 28 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 233 (accept_3_2 25 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 233
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 167 233 (accept_3_2 22 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 167 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 167 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 233 (accept_3_2 19 167 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 233 (accept_3_2 16 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 233 (accept_3_2 13 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 233 (accept_3_2 10 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 233 (accept_3_2 7 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 233 (accept_3_2 4 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 233 (accept_3_2 1 167 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 166 233 (Eq.refl Bool.true) (allA_of_3_0 68 166 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 165 233
  (Eq.refl Bool.true) (allA_succ_of_accept 68 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 233 (accept_3_2 67 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 233 (Polychromatic418967fa.accept_19_9_13_5_1_4351 66 165
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 233 (accept_3_2 64 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 165 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 233 (accept_3_2 61 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 233 (accept_3_2 58 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 233 (accept_3_2 55 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 233
  (Polychromatic418967fa.accept_22_9_11_13_1_10890 53 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 165 233 (accept_3_2 52 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 165 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 165 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 233 (accept_3_2 49 165 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 233 (Polychromatic418967fa.accept_7_6_4_2_1_236
  48 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 233 (accept_3_2 46 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 233 (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 233 (accept_3_2 43 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 233 (accept_3_2 40 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 233 (accept_3_2 37 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 233
  (Polychromatic418967fa.accept_20_15_5_13_1_13894 35 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 165 233 (accept_3_2 34 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 165 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 233 (accept_3_2 31 165 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 233
  (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 233 (accept_3_2 28 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 26
  165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 233 (accept_3_2 25
  165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 233
  (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 233 (accept_3_2 22 165 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 233 (accept_3_2 19 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 17 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 233 (accept_3_2 16 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 165 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 233 (accept_3_2 13 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 165 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 233 (accept_3_2 10 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 233 (Polychromatic418967fa.accept_19_9_13_5_1_4351 9 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 233 (accept_3_2 7 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 233 (accept_3_2 4 165 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 165 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 233 (accept_3_2 1 165 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 164 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 164 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 164 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 164 233 (accept_3_2 67 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 164 233 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 164 233
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 164 233 (accept_3_2 64 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 164 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 164 233 (accept_3_2 61 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 164 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 164 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 164 233 (accept_3_2 58 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 164 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 56 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 164 233 (accept_3_2 55 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 164 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 164 233
  (Polychromatic418967fa.accept_8_5_4_1_1_111 53 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 164 233 (accept_3_2 52 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 164 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 233 (accept_3_2 49 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 164 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 164 233 (accept_3_2 46 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 164 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 233 (accept_3_2 43 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 164 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 164 233 (accept_3_2 40 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 164 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 233 (accept_3_2 37 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 233
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 164 233 (accept_3_2 34 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 164 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 233 (accept_3_2 31 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 233 (accept_3_2 28 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 233 (accept_3_2 25 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 233 (accept_3_2 22 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 233 (accept_3_2 19 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 164 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 233
  (Polychromatic418967fa.accept_10_7_4_3_1_560 17 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 233 (accept_3_2 16 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 233 (accept_3_2 13 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 233
  (Polychromatic418967fa.accept_16_11_4_9_1_851 11 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 233 (accept_3_2 10 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 233 (accept_3_2 7 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 164 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 233 (accept_3_2 4 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 233 (accept_3_2 1 164 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 163 233 (Eq.refl Bool.true) (allA_of_3_0 71 163 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 162 233 (Eq.refl Bool.true) (allA_succ_of_accept 71 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50
  71 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 233 (accept_3_2 70
  162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 162 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 162 233 (Polychromatic418967fa.accept_19_11_10_5_1_5662 68 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 162 233 (accept_3_2 67 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 162 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 162 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 65 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 162 233 (accept_3_2 64 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 162 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 162 233 (accept_3_2 61 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 60 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 162 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 162 233 (accept_3_2 58 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 162 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 57 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 162 233 (Polychromatic418967fa.accept_15_11_12_8_1_739 56 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 233 (accept_3_2 55 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 162
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 162 233
  (Polychromatic418967fa.accept_19_15_10_5_1_5637 53 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 162 233 (accept_3_2 52 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 233 (Polychromatic418967fa.accept_15_5_12_8_1_3168 50 162
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 233 (accept_3_2 49 162
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 233 (accept_3_2 46 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 233
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 44 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 233 (accept_3_2 43 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 162 233 (Polychromatic418967fa.accept_25_17_12_8_1_13942 42 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 162 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 233 (accept_3_2 40 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 233 (accept_3_2 37 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 162 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 233 (accept_3_2 34 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 33 162 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 233
  (Polychromatic418967fa.accept_19_13_10_5_1_11329 32 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 162 233 (accept_3_2 31 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 162 233 (Polychromatic418967fa.accept_19_11_10_5_1_5662 30 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 233 (Polychromatic418967fa.accept_14_1_8_9_1_1312
  29 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 233 (accept_3_2 28
  162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 162 233 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 233 (accept_3_2 25 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 162 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 162 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 233 (accept_3_2 22
  162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 233
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 162 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 233 (accept_3_2 19 162 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 162 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 233 (accept_3_2 16 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 233 (Polychromatic418967fa.accept_17_14_9_12_1_5350 14 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 233 (accept_3_2 13 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 233 (Polychromatic418967fa.accept_16_12_2_9_1_3461 12 162
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 233 (accept_3_2 10 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 233 (Polychromatic418967fa.accept_20_9_2_13_1_6778 9 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 233 (Polychromatic418967fa.accept_19_8_10_5_1_9903 8 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 233 (accept_3_2 7 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 162 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 233
  (Polychromatic418967fa.accept_10_5_2_3_1_239 5 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 233 (accept_3_2 4 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 2 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 233 (accept_3_2 1 162 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 161 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 161 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 233 (Polychromatic418967fa.accept_13_6_5_12_1_307 71 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 233 (accept_3_2 70 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 233
  (Polychromatic418967fa.accept_13_4_5_12_1_751 69 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 161 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 161 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 233 (accept_3_2 67 161 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 161 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 66 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 161 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 161 233 (accept_3_2 64 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 161 233 (Polychromatic418967fa.accept_15_3_11_8_1_4186 63 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 62 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 161 233 (accept_3_2 61 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 161 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 233
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 233 (accept_3_2 58 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 57 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 161 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 233 (accept_3_2 55 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 233
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 161 233 (accept_3_2 52 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 161 233 (Polychromatic418967fa.accept_19_13_9_5_1_8541 51 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 161 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 50 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 233 (accept_3_2 49 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 233
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 233 (accept_3_2 46 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 233 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 233 (Polychromatic418967fa.accept_14_2_7_9_1_2937 44 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 233 (accept_3_2 43 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 233
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 233 (accept_3_2 40 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 233 (Polychromatic418967fa.accept_17_5_8_12_1_6609 39 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 38 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 233 (accept_3_2 37 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 233 (Polychromatic418967fa.accept_27_9_26_17_1_980 36 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 233
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 35 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 233 (accept_3_2 34 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 233 (Polychromatic418967fa.accept_13_7_5_12_1_1305 33 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 233 (accept_3_2 31 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 233 (Polychromatic418967fa.accept_13_4_5_12_1_751 30 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 233
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 29 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 233 (accept_3_2 28 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 233 (Polychromatic418967fa.accept_14_12_7_9_1_726 26 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 233 (accept_3_2 25 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 233 (Polychromatic418967fa.accept_16_8_1_9_1_847 24 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 233
  (Polychromatic418967fa.accept_19_4_9_5_1_8572 23 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 233 (accept_3_2 22 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 233 (accept_3_2 19 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 233
  (Polychromatic418967fa.accept_13_4_5_12_1_751 17 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 233 (accept_3_2 16 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 233 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 233 (accept_3_2 13 161 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 161
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 233
  (Polychromatic418967fa.accept_21_11_14_2_1_6371 11 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 161 233 (accept_3_2 10 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 161 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 161 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 161 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 233 (accept_3_2 7 161 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 233 (Polychromatic418967fa.accept_13_6_5_12_1_307
  6 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 233
  (Polychromatic418967fa.accept_14_5_7_9_1_3828 5 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 233 (accept_3_2 4 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 233 (Polychromatic418967fa.accept_15_3_11_8_1_4186 3 161 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 161 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 233 (accept_3_2 1 161 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 160 233 (Eq.refl Bool.true) (allA_of_3_0 74 160 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 159 233 (Eq.refl Bool.true) (allA_succ_of_accept 74 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2
  74 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 233 (accept_3_2 73
  159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 233
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 72 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 159 233 (Polychromatic418967fa.accept_25_21_9_8_1_13941 71 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 233 (accept_3_2 70 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 233 (accept_3_2 67 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 233 (accept_3_2 64 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 233 (accept_3_2 61 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 233 (accept_3_2 58 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 233 (accept_3_2 55 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 233 (accept_3_2 52 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 233 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 159 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 233 (accept_3_2 49 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 233 (accept_3_2 46 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 233 (accept_3_2 43 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 233 (accept_3_2 40 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 233 (accept_3_2 37 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 233 (Polychromatic418967fa.accept_13_9_3_12_1_2025 35 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 233 (accept_3_2 34 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 159
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 233 (accept_3_2 31 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 233 (accept_3_2 28 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 233 (Polychromatic418967fa.accept_17_10_6_12_1_11635 27 159 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 233 (accept_3_2 25 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 233 (accept_3_2 22 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 233 (accept_3_2 19 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 233 (accept_3_2 16 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 233 (Polychromatic418967fa.accept_13_2_3_12_1_735 15 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 233 (accept_3_2 13 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 233 (accept_3_2 10 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 233 (accept_3_2 7 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 233 (accept_3_2 4 159 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 233 (accept_3_2 1 159 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 158 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 158 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 233 (accept_3_2 73
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 158 233
  (Polychromatic418967fa.accept_11_6_4_2_1_599 72 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 158 233 (accept_3_2 70 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 158 233 (Polychromatic418967fa.accept_7_5_4_2_1_235
  68 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 233 (accept_3_2 67
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 158 233
  (Polychromatic418967fa.accept_9_3_5_8_1_99 66 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 158 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 158 233 (accept_3_2 64 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 158 233 (Polychromatic418967fa.accept_7_6_4_2_1_236
  62 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 233 (accept_3_2 61
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 158 233
  (Polychromatic418967fa.accept_9_6_5_8_1_598 60 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 233 (accept_3_2 58 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 158 233 (accept_3_2 55
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 158 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 158 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 53 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 233 (accept_3_2 52 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 233 (Polychromatic418967fa.accept_11_6_4_2_1_599
  50 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 158 233 (accept_3_2 49
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 158 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 233 (accept_3_2 46 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  44 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 158 233 (accept_3_2 43
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 158 233
  (Polychromatic418967fa.accept_9_6_5_8_1_598 42 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 158 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 233 (accept_3_2 40 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 38
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 158 233 (accept_3_2 37
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 158 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 233 (accept_3_2 34 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 233 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 233 (accept_3_2 31
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 158 233
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 158 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 233 (accept_3_2 28 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 233 (Polychromatic418967fa.accept_7_5_4_2_1_235
  26 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 233 (accept_3_2 25
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 158 233
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 233 (accept_3_2 22 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 233 (Polychromatic418967fa.accept_7_6_4_2_1_236
  20 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 233 (accept_3_2 19
  158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 158 233
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 158 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 233 (accept_3_2 16 158 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 233
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 14 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 233 (accept_3_2 13 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 233 (accept_3_2 10 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 158 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 233 (accept_3_2 7 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 233 (accept_3_2 4 158 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 233 (accept_3_2 1 158 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 157 233 (Eq.refl
  Bool.true) (allA_of_3_0 77 157 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 156 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 156 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 156 233 (accept_3_2 76 156 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 156 233 (Polychromatic418967fa.accept_17_7_3_12_1_4098 75 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 156 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 156 233 (accept_3_2 73 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 156 233 (Polychromatic418967fa.accept_16_8_12_9_1_2569 72 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 156 233 (Polychromatic418967fa.accept_22_5_2_13_1_9228 71 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 233 (accept_3_2 70 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 156 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 156 233 (accept_3_2 67 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 156 233 (Polychromatic418967fa.accept_16_2_12_9_1_2568 66 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 156 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 233 (accept_3_2 64 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 156 233 (Polychromatic418967fa.accept_14_7_2_9_1_2093 63 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 233
  (Polychromatic418967fa.accept_15_2_6_8_1_754 62 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 156 233 (accept_3_2 61 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 156 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 233 (accept_3_2 58 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 156 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 156 233 (accept_3_2 55 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 156 233 (Polychromatic418967fa.accept_21_12_9_2_1_7941 54 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 233 (accept_3_2 52 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 233 (accept_3_2 49 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 156 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 156 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 233 (accept_3_2 46 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 233
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 156 233 (accept_3_2 43 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 156 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 233 (accept_3_2 40 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 156 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 156 233 (accept_3_2 37 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 156 233 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 156 233 (Polychromatic418967fa.accept_14_7_2_9_1_2093 35 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 233 (accept_3_2 34 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 156 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 233 (accept_3_2 31 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 156 233 (Polychromatic418967fa.accept_22_8_2_13_1_10950 30 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 233 (accept_3_2 28 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 233
  (Polychromatic418967fa.accept_22_4_2_13_1_13940 26 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 156 233 (accept_3_2 25 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 156 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 233 (accept_3_2 22 156 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111
  21 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 233 (accept_3_2 19 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 156 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 156 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 17 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 233 (accept_3_2 16 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 233 (accept_3_2 13 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 156 233 (Polychromatic418967fa.accept_19_12_4_5_1_9936 12 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 156 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 233 (accept_3_2 10 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 156 233 (accept_3_2 7 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  156 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 156 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 233 (accept_3_2 4 156 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 233 (Polychromatic418967fa.accept_16_3_12_9_1_8250 3 156 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 233 (accept_3_2 1 156 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 155 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 233 (Polychromatic418967fa.accept_9_5_2_8_1_109
  77 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 233 (accept_3_2 76
  155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 233
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 155 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 233 (accept_3_2 73 155 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 155 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 71 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 233 (accept_3_2 70 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 233 (accept_3_2 67 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 233
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 233 (accept_3_2 64 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 233 (accept_3_2 61 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 233 (accept_3_2 58 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 233 (Polychromatic418967fa.accept_15_11_5_8_1_3157 56 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 233 (accept_3_2 55 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 155 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 233
  (Polychromatic418967fa.accept_16_5_11_9_1_861 53 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 233 (accept_3_2 52 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 233 (accept_3_2 49 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 233 (accept_3_2 46 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 233 (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 233 (accept_3_2 43 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 155 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 233 (accept_3_2 40 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 233 (accept_3_2 37 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 233
  (Polychromatic418967fa.accept_19_16_3_5_1_5684 35 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 233 (accept_3_2 34 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 233 (accept_3_2 31 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 233 (accept_3_2 28 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 233 (accept_3_2 25 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 233 (accept_3_2 22 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 233 (accept_3_2 19 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 233 (accept_3_2 16 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 233 (accept_3_2 13 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 233 (accept_3_2 10 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 233 (Polychromatic418967fa.accept_22_9_1_13_1_7731 9 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 233 (accept_3_2 7 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 155 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 233 (accept_3_2 4 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 233 (accept_3_2 1 155 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 154 233 (Eq.refl Bool.true) (allA_of_3_0 80 154 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 153 233 (Eq.refl Bool.true) (allA_succ_of_accept 80 153 233 (Polychromatic418967fa.accept_6_2_3_5_1_26
  80 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 233 (accept_3_2 79
  153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 78 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 153 233 (Polychromatic418967fa.accept_21_14_6_2_1_4793 77 153 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 233 (accept_3_2 76 153 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 75 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 153 233 (accept_3_2 73 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 153 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 153 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 233 (accept_3_2 70 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 69 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 233 (accept_3_2 67 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 233 (Polychromatic418967fa.accept_15_5_3_8_1_748 65 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 233 (accept_3_2 64 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 153
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 233 (accept_3_2 61 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 233 (accept_3_2 58 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 233 (accept_3_2 55 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 54 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 233 (accept_3_2 52 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 233 (accept_3_2 49 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 233 (accept_3_2 46 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 153 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 233 (accept_3_2 43 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 42 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 233 (accept_3_2 40 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 153 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 233 (accept_3_2 37 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 233 (accept_3_2 34 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 153
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 233 (accept_3_2 31 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 233 (Polychromatic418967fa.accept_18_12_9_17_1_7428 30 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 233 (accept_3_2 28 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 233 (accept_3_2 25 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 233 (accept_3_2 22 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 233 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 153
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 233 (accept_3_2 19 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 233 (accept_3_2 16 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 233 (accept_3_2 13 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 233 (Polychromatic418967fa.accept_11_1_10_2_1_58 12 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 233 (accept_3_2 10 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 233 (accept_3_2 7 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 233 (Polychromatic418967fa.accept_13_6_10_12_1_2049 6 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 233 (Polychromatic418967fa.accept_15_5_3_8_1_748 5 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 233 (accept_3_2 4 153 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 233 (accept_3_2 1 153 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 152 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 152 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 152 233 (accept_3_2 79
  152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 152 233
  (Polychromatic418967fa.accept_23_9_14_3_1_5608 78 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 152 233 (Polychromatic418967fa.accept_14_7_12_9_1_2926 77 152 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 152 233 (accept_3_2 76 152 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 152 233 (Polychromatic418967fa.accept_7_4_5_2_1_243
  74 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 152 233 (accept_3_2 73
  152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 152 233
  (Polychromatic418967fa.accept_22_6_20_13_1_10914 72 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 152 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 152 233 (accept_3_2 70 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 233
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 68 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 152 233 (accept_3_2 67 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 152 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 152 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 65 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 233 (accept_3_2 64 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 233
  (Polychromatic418967fa.accept_11_7_9_2_1_260 62 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 152 233 (accept_3_2 61 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 152 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 152 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 233 (accept_3_2 58 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 233
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 56 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 152 233 (accept_3_2 55 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 54 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 233 (accept_3_2 52 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 233 (accept_3_2 49 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 48 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 233 (accept_3_2 46 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 233
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 44 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 233 (accept_3_2 43 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 41 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 233 (accept_3_2 40 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 233 (accept_3_2 37 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 233 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 233 (accept_3_2 34 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 233 (accept_3_2 31 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 233 (Polychromatic418967fa.accept_17_13_16_12_1_6562 30 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 29 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 233 (accept_3_2 28 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 233
  (Polychromatic418967fa.accept_11_4_9_2_1_259 26 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 233 (accept_3_2 25 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 233 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 233 (accept_3_2 22 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 233
  (Polychromatic418967fa.accept_16_4_8_9_1_4639 20 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 233 (accept_3_2 19 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 233 (accept_3_2 16 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 233 (accept_3_2 13 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 233 (Polychromatic418967fa.accept_16_12_8_9_1_2583 12 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 233 (accept_3_2 10 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 233
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 8 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 233 (accept_3_2 7 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 5 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 233 (accept_3_2 4 152 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 233 (accept_3_2 1 152 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 151 233 (Eq.refl
  Bool.true) (allA_of_3_0 83 151 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 150 233 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 150 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 150 233 (accept_3_2 82 150 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 150 233 (Polychromatic418967fa.accept_20_1_10_13_1_12604 81 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 150 233
  (Polychromatic418967fa.accept_21_17_3_2_1_2111 80 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 150 233 (accept_3_2 79 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 150 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 150 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 233 (accept_3_2 76 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 150 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 74 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 150 233 (accept_3_2 73 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 150 233 (Polychromatic418967fa.accept_19_15_17_5_1_3052 72 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 233 (accept_3_2 70 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 150 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 233 (accept_3_2 67 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 150 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 150 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 233 (accept_3_2 64 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 150 233 (accept_3_2 61 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 150 233 (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 233 (accept_3_2 58 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 150 233 (accept_3_2 55 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 150 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 150 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 233 (accept_3_2 52 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 233 (accept_3_2 49 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 150 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 233 (accept_3_2 46 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 233 (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 150 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 233
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 44 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 233 (accept_3_2 43 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 150 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 42 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 150 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 233 (accept_3_2 40 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 233 (accept_3_2 37 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 150 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 233 (accept_3_2 34 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 233 (accept_3_2 31 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 150 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 150 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 233 (accept_3_2 28 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 233 (accept_3_2 25 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 150 233 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 233 (accept_3_2 22 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 233 (accept_3_2 19 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 233 (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 233 (accept_3_2 16 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 233 (accept_3_2 13 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 150 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 233 (accept_3_2 10 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 233 (accept_3_2 7 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 233 (accept_3_2 4 150 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 233 (accept_3_2 1 150 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 149 233
  (Eq.refl Bool.true) (allA_succ_of_accept 84 149 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 233 (accept_3_2 82 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 81 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 80 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 233 (accept_3_2 79 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 233
  (Polychromatic418967fa.accept_16_13_5_9_1_4682 77 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 233 (accept_3_2 76 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 233 (accept_3_2 73 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 233
  (Polychromatic418967fa.accept_19_14_16_5_1_5668 71 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 149 233 (accept_3_2 70 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 233 (accept_3_2 67 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 66
  149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 233 (accept_3_2 64 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 233 (Polychromatic418967fa.accept_22_19_17_13_1_13939 63 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 62 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 233 (accept_3_2 61 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 233 (Polychromatic418967fa.accept_8_4_5_1_1_299
  60 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 233
  (Polychromatic418967fa.accept_11_4_6_2_1_51 59 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 233 (accept_3_2 58 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 233 (accept_3_2 55 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 233
  (Polychromatic418967fa.accept_27_26_14_17_1_10081 53 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 149 233 (accept_3_2 52 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 50 149
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 233 (accept_3_2 49 149
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 233
  (Polychromatic418967fa.accept_9_3_5_8_1_99 48 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 149 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 233 (accept_3_2 46 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 149 233 (Polychromatic418967fa.accept_16_13_5_9_1_4682 45 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 44 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 233 (accept_3_2 43 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 233 (accept_3_2 40 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 233 (accept_3_2 37 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 233 (accept_3_2 34 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 233
  (Polychromatic418967fa.accept_25_7_24_8_1_13938 32 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 149 233 (accept_3_2 31 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 233 (accept_3_2 28 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 233
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 149 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 26 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 233 (accept_3_2 25 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 233
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 149 233 (accept_3_2 22 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 233 (accept_3_2 19 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 233
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 149 233 (Polychromatic418967fa.accept_16_1_5_9_1_1649 17 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 233 (accept_3_2 16 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 149 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907
  14 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 233 (accept_3_2 13
  149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 233
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 149 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 233 (accept_3_2 10 149 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 149 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 9 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 233
  (Polychromatic418967fa.accept_18_8_5_17_1_1388 8 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 233 (accept_3_2 7 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 233 (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 233 (accept_3_2 4 149 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 149 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 233 (accept_3_2 1 149 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 148 233
  (Eq.refl Bool.true) (allA_of_3_0 86 148 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 147 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 233 (accept_3_2 85 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 84 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 83 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 233 (accept_3_2 82 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 233 (accept_3_2 79 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 77 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 233 (accept_3_2 76 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 233 (accept_3_2 73 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 72 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 233
  (Polychromatic418967fa.accept_15_11_12_8_1_739 71 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 233 (accept_3_2 70 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 233 (accept_3_2 67 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 233 (accept_3_2 64 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 233 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 233 (accept_3_2 61 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 233 (accept_3_2 58 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 233 (accept_3_2 55 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 233
  (Polychromatic418967fa.accept_11_9_4_2_1_600 53 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 233 (accept_3_2 52 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 233 (accept_3_2 49 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 48 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 233 (accept_3_2 46 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 233 (accept_3_2 43 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 233 (accept_3_2 40 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 39 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 233 (accept_3_2 37 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 233 (accept_3_2 34 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 233 (accept_3_2 31 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 233 (accept_3_2 28 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 233 (Polychromatic418967fa.accept_19_8_14_5_1_9919 27 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 233 (accept_3_2 25 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 233 (accept_3_2 22 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 233 (accept_3_2 19 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 233
  (Polychromatic418967fa.accept_11_6_4_2_1_599 17 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 233 (accept_3_2 16 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 233 (accept_3_2 13 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 233 (Polychromatic418967fa.accept_14_12_7_9_1_726 12 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 233 (accept_3_2 10 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 233 (accept_3_2 7 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 233 (accept_3_2 4 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 147 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 233 (accept_3_2 1 147 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 146 233
  (Eq.refl Bool.true) (allA_succ_of_accept 87 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 146 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 146 233 (accept_3_2 85 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 146 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 146 233 (accept_3_2 82 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 146 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 146 233 (accept_3_2 79 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 146 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 146 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 146 233 (accept_3_2 76 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 146 233 (accept_3_2 73 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 146 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 146 233 (accept_3_2 70 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 233 (accept_3_2 67 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 233 (Polychromatic418967fa.accept_15_5_11_8_1_1391 65 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 233 (accept_3_2 64 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 146 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 233
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 62 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 233 (accept_3_2 61 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 233 (accept_3_2 58 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 56 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 233 (accept_3_2 55 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 233 (Polychromatic418967fa.accept_13_2_3_12_1_735 54 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 233 (accept_3_2 52 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 233 (accept_3_2 49 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 233 (accept_3_2 46 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 233 (accept_3_2 43 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 233 (accept_3_2 40 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 233 (accept_3_2 37 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 233 (accept_3_2 34 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 233 (accept_3_2 31 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 233 (accept_3_2 28 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 233
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 233 (accept_3_2 25 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 233 (accept_3_2 22 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 233 (accept_3_2 19 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 233 (accept_3_2 16 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 233 (accept_3_2 13 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 233 (accept_3_2 10 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 233 (accept_3_2 7 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 233 (accept_3_2 4 146 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 233
  (Polychromatic418967fa.accept_13_2_3_12_1_735 2 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 233 (accept_3_2 1 146 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 145 233
  (Eq.refl Bool.true) (allA_of_3_0 89 145 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 144 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 144 233 (accept_3_2 88 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 144 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 87 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 144 233
  (Polychromatic418967fa.accept_13_8_1_12_1_762 86 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 144 233 (accept_3_2 85 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 144 233 (Polychromatic418967fa.accept_25_9_19_8_1_13937 84 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 233 (accept_3_2 82 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 144 233 (Polychromatic418967fa.accept_26_3_14_25_1_13936 81 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 233
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 80 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 144 233 (accept_3_2 79 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 144 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 78 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 144 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 77 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 233 (accept_3_2 76 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 233
  (Polychromatic418967fa.accept_15_14_9_8_1_3165 74 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 144 233 (accept_3_2 73 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 144 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 233 (Polychromatic418967fa.accept_17_3_8_12_1_6573 71 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 233 (accept_3_2 70 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 144 233 (accept_3_2 67 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 144 233 (Polychromatic418967fa.accept_21_3_18_2_1_4750 66 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 144 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 65 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 233 (accept_3_2 64 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 62 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 144 233 (accept_3_2 61 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 144 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 60 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 59 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 233 (accept_3_2 58 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 233
  (Polychromatic418967fa.accept_17_5_8_12_1_6609 56 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 144 233 (accept_3_2 55 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 233 (Polychromatic418967fa.accept_19_15_11_5_1_5713 53 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 233 (accept_3_2 52 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 233 (Polychromatic418967fa.accept_19_13_11_5_1_5692 51 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 233
  (Polychromatic418967fa.accept_13_11_1_12_1_742 50 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 233 (accept_3_2 49 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 233 (accept_3_2 46 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 233 (Polychromatic418967fa.accept_21_3_18_2_1_4750 45 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 233
  (Polychromatic418967fa.accept_13_5_1_12_1_740 44 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 233 (accept_3_2 43 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 144 233 (Polychromatic418967fa.accept_29_13_28_1_1_13935 42 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 233 (accept_3_2 40 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 233
  (Polychromatic418967fa.accept_17_4_8_12_1_9165 38 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 233 (accept_3_2 37 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 36 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 233 (Polychromatic418967fa.accept_19_16_11_5_1_11315 35 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 233 (accept_3_2 34 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 233
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 32 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 233 (accept_3_2 31 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 144 233 (Polychromatic418967fa.accept_14_2_4_9_1_2121 30 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 233 (accept_3_2 28 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 233 (accept_3_2 25 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 233 (Polychromatic418967fa.accept_20_3_4_13_1_3824 23 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 233 (accept_3_2 22 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 233 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 233 (accept_3_2 19 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 17 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 233 (accept_3_2 16 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 233 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 144
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 233
  (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 233 (accept_3_2 13 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 233 (accept_3_2 10 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 144 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 233
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 233 (accept_3_2 7 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  144 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 144 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 233 (accept_3_2 4 144 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 233 (Polychromatic418967fa.accept_11_3_1_2_1_1063 3 144 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 233
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 233 (accept_3_2 1 144 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 143 233
  (Eq.refl Bool.true) (allA_succ_of_accept 90 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 233
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 233 (accept_3_2 88 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 233 (Polychromatic418967fa.accept_17_2_7_12_1_1078 87 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 233 (accept_3_2 85 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 233 (Polychromatic418967fa.accept_19_8_10_5_1_9903 84 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 83 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 233 (accept_3_2 82 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 233 (Polychromatic418967fa.accept_20_1_3_13_1_8217 81 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 233 (Polychromatic418967fa.accept_22_14_11_13_1_13934 80 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 233 (accept_3_2 79 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 233
  (Polychromatic418967fa.accept_21_14_17_2_1_11069 77 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 143 233 (accept_3_2 76 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 233 (accept_3_2 73 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 233
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 72 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 143 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 233 (accept_3_2 70 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 143 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249
  68 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 233 (accept_3_2 67
  143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 143 233 (Polychromatic418967fa.accept_19_8_10_5_1_9903 65 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 233 (accept_3_2 64 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 143 233 (Polychromatic418967fa.accept_22_19_11_13_1_10981 63 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 233 (accept_3_2 61 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 233 (Polychromatic418967fa.accept_19_3_10_5_1_4314 60 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 233 (Polychromatic418967fa.accept_19_2_10_5_1_5639 59 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 233 (accept_3_2 58 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 233
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 56 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 233 (accept_3_2 55 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 233 (Polychromatic418967fa.accept_17_2_7_12_1_1078 53 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 233 (accept_3_2 52 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 233 (Polychromatic418967fa.accept_19_13_10_5_1_11329 51
  143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 233 (accept_3_2 49 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 233 (accept_3_2 46 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 233 (Polychromatic418967fa.accept_19_7_10_5_1_3090 45 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 233
  (Polychromatic418967fa.accept_20_4_3_13_1_8257 44 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 233 (accept_3_2 43 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 233 (accept_3_2 40 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 233 (Polychromatic418967fa.accept_17_5_7_12_1_1951 39 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 233 (accept_3_2 37 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 233 (Polychromatic418967fa.accept_19_16_10_5_1_7106 35 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 233 (accept_3_2 34 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 233
  (Polychromatic418967fa.accept_19_13_10_5_1_11329 32 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 143 233 (accept_3_2 31 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 143 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 233 (accept_3_2 28 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 233 (Polychromatic418967fa.accept_7_6_3_2_1_461
  27 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 233 (accept_3_2 25 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 233 (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 233 (Polychromatic418967fa.accept_26_23_13_25_1_13933 23 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 233 (accept_3_2 22 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 233 (Polychromatic418967fa.accept_17_4_7_12_1_6556 21 143
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 233
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 233 (accept_3_2 19 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 233 (Polychromatic418967fa.accept_22_17_11_13_1_13932 17 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 233 (accept_3_2 16 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 233 (accept_3_2 13 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 233 (Polychromatic418967fa.accept_19_11_10_5_1_5662 11 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 233 (accept_3_2 10 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 233 (Polychromatic418967fa.accept_21_9_17_2_1_9537 9 143
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 233
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 233 (accept_3_2 7 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 233 (accept_3_2 4 143 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 233 (Polychromatic418967fa.accept_17_3_7_12_1_2016 3 143 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 233 (accept_3_2 1 143 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 142 233
  (Eq.refl Bool.true) (allA_of_3_0 92 142 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 141 233 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 233 (accept_3_2 91 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 233
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 89 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 233 (accept_3_2 88 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 87 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 233 (accept_3_2 85 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 83 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 233 (accept_3_2 82 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 81 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 233 (accept_3_2 79 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 78 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 77 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 233 (accept_3_2 76 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 233 (accept_3_2 73 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 233
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 71 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 233 (accept_3_2 70 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 233 (accept_3_2 67 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 65 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 233 (accept_3_2 64 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 233 (accept_3_2 61 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 233 (accept_3_2 58 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 233 (accept_3_2 55 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 233 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 141 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 233
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 53 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 141 233 (accept_3_2 52 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 141 233 (Polychromatic418967fa.accept_11_7_9_2_1_260 51 141 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 141 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 233 (accept_3_2 49 141 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 233 (Polychromatic418967fa.accept_7_6_1_2_1_230
  48 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 233 (accept_3_2 46 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 233 (accept_3_2 43 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 233 (accept_3_2 40 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 233 (accept_3_2 37 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 233
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 35 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 233 (accept_3_2 34 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 233 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 233 (accept_3_2 31 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 233 (accept_3_2 28 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 233 (accept_3_2 25 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 233 (accept_3_2 22 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 233 (accept_3_2 19 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 233 (accept_3_2 16 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 233 (Polychromatic418967fa.accept_11_4_9_2_1_259 15 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 233 (accept_3_2 13 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 233 (accept_3_2 10 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 233 (Polychromatic418967fa.accept_17_9_5_12_1_6606 9 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 233 (accept_3_2 7 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 233 (accept_3_2 4 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 233 (accept_3_2 1 141 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 140
  233 (Eq.refl Bool.true) (allA_succ_of_accept 93 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 92 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 140 233 (accept_3_2 91 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 140 233 (Polychromatic418967fa.accept_21_6_14_2_1_7980 90 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 140 233 (Polychromatic418967fa.accept_13_11_10_12_1_1338 89 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 140 233 (accept_3_2 88 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 140 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 86 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 140 233 (accept_3_2 85 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 140 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 140 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 83 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 140 233 (accept_3_2 82 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 140 233
  (Polychromatic418967fa.accept_13_2_10_12_1_757 80 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 140 233 (accept_3_2 79 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 140 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 140 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 140 233 (accept_3_2 76 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 74 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 140 233 (accept_3_2 73 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 140 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 140 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 71 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 140 233 (accept_3_2 70 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 233
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 68 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 140 233 (accept_3_2 67 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 140 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 65 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 233 (accept_3_2 64 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 233 (accept_3_2 61 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 233 (Polychromatic418967fa.accept_13_7_10_12_1_2047 59 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 233 (accept_3_2 58 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 140 233 (accept_3_2 55 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 140 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 54 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 53 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 233 (accept_3_2 52 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 50 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 233 (accept_3_2 49 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 233 (accept_3_2 46 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 44 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 233 (accept_3_2 43 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 233 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 233 (accept_3_2 40 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 233 (accept_3_2 37 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 233 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 233 (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 233 (accept_3_2 34 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 233
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 140 233 (accept_3_2 31 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 140 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 140 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 233 (accept_3_2 28 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27
  140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 233 (accept_3_2 25 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 233 (Polychromatic418967fa.accept_25_23_15_8_1_13931 23 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 233 (accept_3_2 22 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 233 (accept_3_2 19 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 233 (Polychromatic418967fa.accept_19_17_7_5_1_1883 17 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 233 (accept_3_2 16 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 233 (accept_3_2 13 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 140 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 233 (accept_3_2 10 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 233
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 233 (accept_3_2 7 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 233 (accept_3_2 4 140 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 233 (accept_3_2 1 140 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 139
  233 (Eq.refl Bool.true) (allA_of_3_0 95 139 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 138 233
  (Eq.refl Bool.true) (allA_succ_of_accept 95 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 138 233 (accept_3_2 94 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 138 233 (Polychromatic418967fa.accept_21_9_12_2_1_4781 93 138
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 138 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 92 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 138 233 (accept_3_2 91 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 138 233 (Polychromatic418967fa.accept_21_6_12_2_1_4801 90 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 138 233 (Polychromatic418967fa.accept_17_4_2_12_1_6554 89 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 233 (accept_3_2 88 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 138 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 86 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 138 233 (accept_3_2 85 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 138 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 84 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 233 (accept_3_2 82 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 138 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 80 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 138 233 (accept_3_2 79 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 138 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 78 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 138 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 233 (accept_3_2 76 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 233 (accept_3_2 73 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 138 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 233 (accept_3_2 70 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 138 233 (accept_3_2 67 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 138 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 233 (accept_3_2 64 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 233
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 62 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 138 233 (accept_3_2 61 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 138 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 138 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 233 (accept_3_2 58 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 233
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 57 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 138 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 138 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 233 (accept_3_2 55 138 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 138 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 54 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 138 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 138 233 (accept_3_2 52 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 138 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 233 (accept_3_2 49 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 233 (Polychromatic418967fa.accept_11_4_6_2_1_51 48 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 138 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 233 (accept_3_2 46 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 138 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 138 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 233 (accept_3_2 43 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 233 (accept_3_2 40 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 138 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 233 (accept_3_2 37 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 138 233 (accept_3_2 34 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 138 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 138 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 233 (accept_3_2 31 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 233 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 233
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 233 (accept_3_2 28 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 138 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 233 (accept_3_2 25 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 233 (accept_3_2 22 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 138 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 138 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 233 (accept_3_2 19 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 138 233 (accept_3_2 16 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 138 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 233 (accept_3_2 13 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 233 (accept_3_2 10 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  138 233 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 138 233 (Polychromatic418967fa.accept_20_8_18_13_1_8326 8 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 233 (accept_3_2 7 138 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 138 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 233
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 233 (accept_3_2 4 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  138 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 138 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 233 (accept_3_2 1 138 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 138
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 137
  233 (Eq.refl Bool.true) (allA_succ_of_accept 96 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 233 (accept_3_2 94 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 93 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 233 (Polychromatic418967fa.accept_18_2_11_17_1_4773 92 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 233 (accept_3_2 91 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 90 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 89 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 233 (accept_3_2 88 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 87 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 233 (accept_3_2 85 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 83 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 233 (accept_3_2 82 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 233 (Polychromatic418967fa.accept_15_6_2_8_1_2223 81 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 233 (Polychromatic418967fa.accept_21_17_11_2_1_7953 80 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 233 (accept_3_2 79 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 77 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 233 (accept_3_2 76 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 74 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 233 (accept_3_2 73 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 233 (Polychromatic418967fa.accept_14_2_11_9_1_2925 72 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 233
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 71 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 233 (accept_3_2 70 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 68 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 233 (accept_3_2 67 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 65 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 233 (accept_3_2 64 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 63 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 233 (accept_3_2 61 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 59 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 233 (accept_3_2 58 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 57 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 233 (accept_3_2 55 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 233
  (Polychromatic418967fa.accept_19_15_4_5_1_11338 53 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 137 233 (accept_3_2 52 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 137 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 50 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 233 (accept_3_2 49 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236
  48 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 233 (accept_3_2 46 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 233 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 233 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 233 (accept_3_2 43 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 233
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 233 (accept_3_2 40 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 233 (Polychromatic418967fa.accept_18_2_11_17_1_4773 38 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 233 (accept_3_2 37 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 233 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 137
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 233
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 233 (accept_3_2 34 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 233 (accept_3_2 31 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 233
  (Polychromatic418967fa.accept_25_4_12_8_1_6786 29 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 233 (accept_3_2 28 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 233 (accept_3_2 25 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 233 (accept_3_2 22 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 233 (accept_3_2 19 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 233 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 233
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 17 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 233 (accept_3_2 16 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 233 (accept_3_2 13 137 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 233
  (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 233 (accept_3_2 10 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 233 (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 137 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 233 (accept_3_2 7 137 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 6
  137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 233
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 233 (accept_3_2 4 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 137 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 233 (Polychromatic418967fa.accept_14_2_11_9_1_2925 2 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 233 (accept_3_2 1 137 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 137
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  136 233 (Eq.refl Bool.true) (allA_of_3_0 98 136 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 135 233
  (Eq.refl Bool.true) (allA_succ_of_accept 98 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 233 (accept_3_2 97 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 233 (Polychromatic418967fa.accept_17_11_16_12_1_1984 96
  135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 233
  (Polychromatic418967fa.accept_13_4_5_12_1_751 95 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 233 (accept_3_2 94 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 93 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 233 (accept_3_2 91 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 89 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 233 (accept_3_2 88 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 87 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 233 (accept_3_2 85 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 233 (Polychromatic418967fa.accept_13_6_5_12_1_307 84 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 233
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 83 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 233 (accept_3_2 82 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 233 (accept_3_2 79 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 233 (accept_3_2 76 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 233 (Polychromatic418967fa.accept_19_18_2_5_1_5682 75 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 233 (accept_3_2 73 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 233
  (Polychromatic418967fa.accept_13_6_5_12_1_307 71 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 233 (accept_3_2 70 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 69 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 233 (accept_3_2 67 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 233
  (Polychromatic418967fa.accept_19_8_2_5_1_5678 65 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 233 (accept_3_2 64 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 233 (Polychromatic418967fa.accept_23_17_20_3_1_13930 63 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 233 (accept_3_2 61 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 233 (Polychromatic418967fa.accept_13_8_5_12_1_2755 60 135
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 233
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 59 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 233 (accept_3_2 58 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 233 (accept_3_2 55 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 233
  (Polychromatic418967fa.accept_13_1_5_12_1_306 53 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 233 (accept_3_2 52 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 233 (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 233 (accept_3_2 49 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 233 (accept_3_2 46 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 233 (Polychromatic418967fa.accept_11_1_3_2_1_1090 45 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 233 (accept_3_2 43 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 233
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 41 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 233 (accept_3_2 40 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 233 (Polychromatic418967fa.accept_28_11_23_9_1_13929 39 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 233 (accept_3_2 37 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 233 (Polychromatic418967fa.accept_19_17_2_5_1_7085 36 135
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 233
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 35 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 233 (accept_3_2 34 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 233 (accept_3_2 31 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 233
  (Polychromatic418967fa.accept_16_13_7_9_1_2606 29 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 233 (accept_3_2 28 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 233 (accept_3_2 25 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 233 (Polychromatic418967fa.accept_16_8_7_9_1_7052 24 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 233
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 23 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 233 (accept_3_2 22 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 233 (accept_3_2 19 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 233 (accept_3_2 16 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 233 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 233 (accept_3_2 13 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 135 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 233
  (Polychromatic418967fa.accept_17_11_16_12_1_1984 11 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 233 (accept_3_2 10 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 135 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 135 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 233 (accept_3_2 7 135 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 233
  (Polychromatic418967fa.accept_20_5_15_13_1_5235 5 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 233 (accept_3_2 4 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 233 (Polychromatic418967fa.accept_16_3_7_9_1_3474 3 135 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 233 (accept_3_2 1 135 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  134 233 (Eq.refl Bool.true) (allA_succ_of_accept 99 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 134 233
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 98 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 134 233 (accept_3_2 97 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 134 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 96 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 134 233 (accept_3_2 94 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 92 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 134 233 (accept_3_2 91 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 134 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 90 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 134 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 89 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 134 233 (accept_3_2 88 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 134 233
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 86 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 134 233 (accept_3_2 85 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 134 233 (Polychromatic418967fa.accept_15_9_14_8_1_1396 84 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 134 233 (accept_3_2 82 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 134 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 134 233 (accept_3_2 79 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 134 233 (Polychromatic418967fa.accept_21_15_8_2_1_11079 78 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 134 233 (Polychromatic418967fa.accept_10_7_4_3_1_560 77 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 134 233 (accept_3_2 76 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 233
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 74 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 134 233 (accept_3_2 73 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 134 233 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 233 (accept_3_2 70 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 68 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 233 (accept_3_2 67 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 233 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 233 (accept_3_2 64 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 233 (accept_3_2 61 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 233 (Polychromatic418967fa.accept_13_8_4_12_1_2753 60 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 233 (accept_3_2 58 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 233 (accept_3_2 55 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 233 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 233 (Polychromatic418967fa.accept_19_15_1_5_1_3013 53 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 233 (accept_3_2 52 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 233
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 50 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 134 233 (accept_3_2 49 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 134 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 134 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 233 (accept_3_2 46 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 233 (accept_3_2 43 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 233 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 233 (accept_3_2 40 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 233
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 233 (accept_3_2 37 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 233 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 233 (accept_3_2 34 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 233 (accept_3_2 31 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 233 (Polychromatic418967fa.accept_22_8_2_13_1_10950 30 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 233 (Polychromatic418967fa.accept_10_9_4_3_1_539 29 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 233 (accept_3_2 28 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 233
  (Polychromatic418967fa.accept_21_5_8_2_1_11063 26 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 233 (accept_3_2 25 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 233 (accept_3_2 22 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 233
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 233 (accept_3_2 19 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 233 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 233 (accept_3_2 16 134 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 233
  (Polychromatic418967fa.accept_17_14_15_12_1_1921 14 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 134 233 (accept_3_2 13 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 134 233 (Polychromatic418967fa.accept_19_12_1_5_1_9924 12 134 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 233 (accept_3_2 10 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 233
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 233 (accept_3_2 7 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 233 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 233 (Polychromatic418967fa.accept_13_5_4_12_1_2058 5 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 233 (accept_3_2 4 134 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 233
  (Polychromatic418967fa.accept_13_2_4_12_1_745 2 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 233 (accept_3_2 1 134 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 133 233 (Eq.refl Bool.true) (allA_of_3_0 101 133 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 132
  233 (Eq.refl Bool.true) (allA_succ_of_accept 101 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 132 233 (accept_3_2 100 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 99
  132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 132 233
  (Polychromatic418967fa.accept_21_14_6_2_1_4793 98 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 132 233 (accept_3_2 97 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 132 233 (Polychromatic418967fa.accept_13_5_2_12_1_1301 96 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 95 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 132 233 (accept_3_2 94 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 132 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 93 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 132 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 92 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 132 233 (accept_3_2 91 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 132 233 (Polychromatic418967fa.accept_20_10_12_13_1_8268 90 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 132 233 (Polychromatic418967fa.accept_19_13_18_5_1_8619 89 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 233 (accept_3_2 88 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 87
  132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 86 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 132 233 (accept_3_2 85 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 132 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 132 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 83 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 233 (accept_3_2 82 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 132 233 (accept_3_2 79 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 132 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 77 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 233 (accept_3_2 76 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 75 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 74 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 132 233 (accept_3_2 73 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 132 233 (Polychromatic418967fa.accept_16_8_4_9_1_4666 72 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 233 (accept_3_2 70 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 132 233 (accept_3_2 67 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 132 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 233 (accept_3_2 64 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 63 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 233
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 62 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 132 233 (accept_3_2 61 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 132 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 233 (accept_3_2 58 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57
  132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 233 (accept_3_2 55 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 233 (Polychromatic418967fa.accept_21_12_6_2_1_7950 54 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 233 (accept_3_2 52 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 233 (Polychromatic418967fa.accept_10_1_2_3_1_1910 51 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 233 (accept_3_2 49 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 233 (accept_3_2 46 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 233
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 44 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 233 (accept_3_2 43 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 233 (Polychromatic418967fa.accept_13_3_2_12_1_2797 42 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 132 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 233 (accept_3_2 40 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 233 (accept_3_2 37 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 233 (Polychromatic418967fa.accept_10_5_2_3_1_239 35 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 233 (accept_3_2 34 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 233 (Polychromatic418967fa.accept_15_3_12_8_1_738 33 132
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 233 (accept_3_2 31 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 233 (accept_3_2 28 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 233 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 132 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 233
  (Polychromatic418967fa.accept_15_11_12_8_1_739 26 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 233 (accept_3_2 25 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 233 (accept_3_2 22 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 233 (accept_3_2 19 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 233 (accept_3_2 16 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 233
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 233 (accept_3_2 13 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 233 (accept_3_2 10 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 233 (Polychromatic418967fa.accept_19_9_18_5_1_7101 9 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 233 (accept_3_2 7 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 233 (Polychromatic418967fa.accept_13_6_2_12_1_2802 6 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 233 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 233 (accept_3_2 4 132 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 233
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 233 (accept_3_2 1 132 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 131 233 (Eq.refl Bool.true) (allA_succ_of_accept 102 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 131 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 101 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 131 233 (accept_3_2 100 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 131 233 (Polychromatic418967fa.accept_13_8_1_12_1_762 99 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 98 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 233 (accept_3_2 97 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 131 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 96 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 95 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 131 233 (accept_3_2 94 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 93 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 131 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 92 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 233 (accept_3_2 91 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 233
  (Polychromatic418967fa.accept_11_1_10_2_1_58 89 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 233 (accept_3_2 88 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 233 (accept_3_2 85 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 84 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 233 (accept_3_2 82 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 233 (accept_3_2 79 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 233
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 77 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 233 (accept_3_2 76 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 233 (accept_3_2 73 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 233 (Polychromatic418967fa.accept_10_2_1_3_1_233 72 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 233
  (Polychromatic418967fa.accept_16_7_3_9_1_2557 71 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 233 (accept_3_2 70 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 68 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 233 (accept_3_2 67 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 131 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 233 (accept_3_2 64 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 233 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 233 (accept_3_2 61 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 233 (accept_3_2 58 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 233 (accept_3_2 55 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 53 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 233 (accept_3_2 52 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 233 (accept_3_2 49 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 233 (accept_3_2 46 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 233 (Polychromatic418967fa.accept_13_5_1_12_1_740 44 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 233 (accept_3_2 43 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 233
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 41 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 233 (accept_3_2 40 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 233 (accept_3_2 37 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 233 (Polychromatic418967fa.accept_22_14_21_13_1_13901 36 131 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 233
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 233 (accept_3_2 34 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 233 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 233 (accept_3_2 31 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 233
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 233 (accept_3_2 28 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 233 (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 233 (accept_3_2 25 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 233
  (Polychromatic418967fa.accept_11_1_10_2_1_58 23 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 233 (accept_3_2 22 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 233 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 233 (accept_3_2 19 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 233
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 233 (accept_3_2 16 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 233 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 233 (accept_3_2 13 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 233 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 233
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 233 (accept_3_2 10 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 233 (Polychromatic418967fa.accept_22_9_21_13_1_10830 9 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 233 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 233 (accept_3_2 7 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 233
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 233 (accept_3_2 4 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 233 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 233 (accept_3_2 1 131 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 130 233 (Eq.refl Bool.true) (allA_of_3_0 104 130 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 129
  233 (Eq.refl Bool.true) (allA_succ_of_accept 104 129 233 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 233 (accept_3_2 103 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 233
  (Polychromatic418967fa.accept_20_2_9_13_1_2599 102 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 129 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 101 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 233 (accept_3_2 100 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 99 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 233 (accept_3_2 97 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 129 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 95 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 233 (accept_3_2 94 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 233 (Polychromatic418967fa.accept_11_5_8_2_1_588 93 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 233 (accept_3_2 91 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 233 (accept_3_2 88 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 87 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 233 (accept_3_2 85 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 233 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 233 (accept_3_2 82 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 233 (Polychromatic418967fa.accept_21_18_3_2_1_13928 81 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 233 (accept_3_2 79 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 233 (accept_3_2 76 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 233 (accept_3_2 73 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 233 (Polychromatic418967fa.accept_16_8_1_9_1_847 72 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 233 (accept_3_2 70 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 233 (accept_3_2 67 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 233 (Polychromatic418967fa.accept_10_6_9_3_1_935 66 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 65 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 233 (accept_3_2 64 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 233 (accept_3_2 61 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 233 (accept_3_2 58 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 233 (accept_3_2 55 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 233 (Polychromatic418967fa.accept_16_5_1_9_1_4621 53 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 233 (accept_3_2 52 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 233 (accept_3_2 49 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 233 (accept_3_2 46 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 233 (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 233 (accept_3_2 43 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 233 (accept_3_2 40 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 233 (accept_3_2 37 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 233 (Polychromatic418967fa.accept_21_14_3_2_1_12567 35 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 233 (accept_3_2 34 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 233 (accept_3_2 31 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 233 (Polychromatic418967fa.accept_19_11_15_5_1_5699 30 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 233 (accept_3_2 28 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 233 (accept_3_2 25 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 233 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 233 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 233 (accept_3_2 22 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 233 (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 233 (accept_3_2 19 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 233 (Polychromatic418967fa.accept_15_3_9_8_1_3164 18 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 233 (Polychromatic418967fa.accept_15_2_9_8_1_736 17 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 233 (accept_3_2 16 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 233 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 233 (accept_3_2 13 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 233 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 233 (accept_3_2 10 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 233 (Polychromatic418967fa.accept_19_9_15_5_1_5666 9 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 233 (accept_3_2 7 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 233 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 233 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 233 (accept_3_2 4 129 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 233 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 233 (accept_3_2 1 129 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 128 233 (Eq.refl Bool.true) (allA_succ_of_accept 105 128 233
  (Polychromatic418967fa.accept_6_3_2_5_1_32 105 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 104 128 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 128 233 (accept_3_2 103 128 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 102 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 128 233
  (Polychromatic418967fa.accept_10_1_8_3_1_947 101 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 128 233 (accept_3_2 100 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 128 233 (Polychromatic418967fa.accept_12_2_8_5_1_408 98 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 128 233 (accept_3_2 97 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 128 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 96 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 128 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 95 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 128 233 (accept_3_2 94 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 128 233 (Polychromatic418967fa.accept_13_1_11_12_1_1322 92 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 128 233 (accept_3_2 91 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 128 233 (Polychromatic418967fa.accept_17_5_9_12_1_9156 90 128
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 128 233
  (Polychromatic418967fa.accept_17_4_9_12_1_9167 89 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 128 233 (accept_3_2 88 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 86 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 128 233 (accept_3_2 85 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 128 233
  (Polychromatic418967fa.accept_18_11_2_17_1_3490 83 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 128 233 (accept_3_2 82 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 233 (Polychromatic418967fa.accept_18_8_2_17_1_4782 80 128
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 128 233 (accept_3_2 79 128
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 128 233
  (Polychromatic418967fa.accept_9_6_2_8_1_592 78 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 233 (accept_3_2 76 128 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 233 (Polychromatic418967fa.accept_12_2_8_5_1_408
  74 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 233 (accept_3_2 73
  128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 128 233
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 128 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 71 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 233 (accept_3_2 70 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 233 (accept_3_2 67 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 65 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 233 (accept_3_2 64 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 233 (accept_3_2 61 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 233 (accept_3_2 58 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 128 233 (accept_3_2 55 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 128 233 (Polychromatic418967fa.accept_19_16_14_5_1_9920 54 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 128 233 (Polychromatic418967fa.accept_11_9_7_2_1_1068 53 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 233 (accept_3_2 52 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 233 (accept_3_2 49 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 233 (Polychromatic418967fa.accept_18_11_2_17_1_3490 47 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 233 (accept_3_2 46 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 233
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 44 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 233 (accept_3_2 43 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 233 (accept_3_2 40 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 233 (accept_3_2 37 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 233 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 128 233 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 233 (accept_3_2 34 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 233 (accept_3_2 31 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 233 (Polychromatic418967fa.accept_18_11_2_17_1_3490 29 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 233 (accept_3_2 28 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 233
  (Polychromatic418967fa.accept_10_6_8_3_1_930 26 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 233 (accept_3_2 25 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 233 (accept_3_2 22 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 233
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 233 (accept_3_2 19 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 233 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 233 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 233 (accept_3_2 16 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 233
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 233 (accept_3_2 13 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 233 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 233 (Polychromatic418967fa.accept_10_1_8_3_1_947 11 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 233 (accept_3_2 10 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 233
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 8 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 233 (accept_3_2 7 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 233 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 233 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 233 (accept_3_2 4 128 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 233 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 233
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 233 (accept_3_2 1 128 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 127 233 (Eq.refl Bool.true) (allA_of_3_0 107 127 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 126 233 (Eq.refl Bool.true) (allA_succ_of_accept 107 126 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 107 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 126 233 (accept_3_2 106 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 126 233 (Polychromatic418967fa.accept_17_3_7_12_1_2016 105 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 126 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 104 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 233 (accept_3_2 103 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 126 233
  (Polychromatic418967fa.accept_19_7_12_5_1_7123 102 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 126 233 (Polychromatic418967fa.accept_13_10_9_12_1_2814 101 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 126 233 (accept_3_2 100 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 99 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 126 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 98 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 126 233 (accept_3_2 97 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 126 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 96 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 233 (accept_3_2 94 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 233 (Polychromatic418967fa.accept_19_17_12_5_1_13927 93 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 126 233
  (Polychromatic418967fa.accept_15_2_6_8_1_754 92 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 126 233 (accept_3_2 91 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 126 233 (Polychromatic418967fa.accept_17_5_7_12_1_1951 90 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 126 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 89 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 233 (accept_3_2 88 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 233
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 86 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 126 233 (accept_3_2 85 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 126 233 (Polychromatic418967fa.accept_16_4_14_9_1_4657 84 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 233 (accept_3_2 82 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 233
  (Polychromatic418967fa.accept_19_4_12_5_1_8615 80 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 233 (accept_3_2 79 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 126 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 126 233 (Polychromatic418967fa.accept_10_7_6_3_1_927 77 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 233 (accept_3_2 76 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 233
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 74 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 126 233 (accept_3_2 73 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 126 233 (Polychromatic418967fa.accept_17_4_7_12_1_6556 72 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 233 (accept_3_2 70 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 69 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 233
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 68 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 126 233 (accept_3_2 67 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 126 233 (Polychromatic418967fa.accept_19_9_12_5_1_5695 66 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 126 233 (Polychromatic418967fa.accept_19_8_12_5_1_7122 65 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 233 (accept_3_2 64 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 233
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 62 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 126 233 (accept_3_2 61 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 126 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 60 126 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 233 (accept_3_2 58 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 233 (Polychromatic418967fa.accept_10_7_6_3_1_927
  57 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 233
  (Polychromatic418967fa.accept_17_5_7_12_1_1951 56 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 126 233 (accept_3_2 55 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 126 233 (Polychromatic418967fa.accept_17_3_7_12_1_2016 54 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 233 (Polychromatic418967fa.accept_16_5_14_9_1_2572 53 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 233 (accept_3_2 52 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 233
  (Polychromatic418967fa.accept_22_6_16_13_1_13925 50 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 126 233 (accept_3_2 49 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 126 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 126 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 233 (accept_3_2 46 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 233
  (Polychromatic418967fa.accept_19_7_12_5_1_7123 45 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 44 126 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 233 (accept_3_2 43 126 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 126 233 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 233
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 41 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 233 (accept_3_2 40 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 126 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 233 (accept_3_2 37 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 126 233 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 126
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 233 (accept_3_2 34 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 126 233 (Polychromatic418967fa.accept_22_11_16_13_1_13926 33 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 233 (Polychromatic418967fa.accept_15_2_6_8_1_754 32 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 233 (accept_3_2 31 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 233 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 126
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 233
  (Polychromatic418967fa.accept_10_9_6_3_1_545 29 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 233 (accept_3_2 28 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 126 233 (Polychromatic418967fa.accept_19_7_12_5_1_7123 26 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 233 (accept_3_2 25 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 233 (Polychromatic418967fa.accept_22_2_16_13_1_10861 24
  126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 233 (accept_3_2 22 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 126 233 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 126 233 (Polychromatic418967fa.accept_16_4_14_9_1_4657 20 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 233 (accept_3_2 19 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 126
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 233
  (Polychromatic418967fa.accept_10_7_6_3_1_927 17 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 233 (accept_3_2 16 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 126 233 (Polychromatic418967fa.accept_15_14_6_8_1_1410 14 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 233 (accept_3_2 13 126 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 233 (Polychromatic418967fa.accept_23_12_11_3_1_13899 12
  126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 233
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 233 (accept_3_2 10 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  126 233 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 126 233 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 233 (accept_3_2 7 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 233 (Polychromatic418967fa.accept_22_6_16_13_1_13925 6 126 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 233
  (Polychromatic418967fa.accept_16_5_14_9_1_2572 5 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 233 (accept_3_2 4 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  126 233 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 126 233 (Polychromatic418967fa.accept_15_2_6_8_1_754 2 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 233 (accept_3_2 1 126 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 126
  233))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 125 233 (Eq.refl Bool.true) (allA_succ_of_accept 108 125 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 108 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 125 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 107 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 233 (accept_3_2 106 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 125 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 105 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 104 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 125 233 (accept_3_2 103 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 102 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 101 125
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 233 (accept_3_2 100 125
  233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 99 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 125 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 98 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 125 233 (accept_3_2 97 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 125 233 (Polychromatic418967fa.accept_13_5_8_12_1_2759 96 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 95 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 233 (accept_3_2 94 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 93 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 92 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 233 (accept_3_2 91 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 233 (Polychromatic418967fa.accept_19_14_11_5_1_11302 90 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 233
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 89 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 233 (accept_3_2 88 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 86 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 233 (accept_3_2 85 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 84 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 233
  (Polychromatic418967fa.accept_11_6_4_2_1_599 83 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 233 (accept_3_2 82 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 81 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 80 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 233 (accept_3_2 79 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 78 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 77 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 233 (accept_3_2 76 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 75 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 233 (accept_3_2 73 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 125 233 (accept_3_2 70 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 125 233 (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 125 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 68 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 233 (accept_3_2 67 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 233
  (Polychromatic418967fa.accept_16_1_13_9_1_2551 65 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 233 (accept_3_2 64 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 233 (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 62 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 233 (accept_3_2 61 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 59 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 233 (accept_3_2 58 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 233 (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 233 (accept_3_2 55 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 233 (Polychromatic418967fa.accept_16_6_13_9_1_4690 54 125
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 233 (accept_3_2 52 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 233 (Polychromatic418967fa.accept_19_13_11_5_1_5692 51 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 50 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 233 (accept_3_2 49 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 233 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 233
  (Polychromatic418967fa.accept_10_7_5_3_1_542 47 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 233 (accept_3_2 46 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 44 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 233 (accept_3_2 43 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 233
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 41 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 233 (accept_3_2 40 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 233 (accept_3_2 37 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 233
  (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 233 (accept_3_2 34 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 233 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 233 (accept_3_2 31 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 233 (Polychromatic418967fa.accept_13_4_8_12_1_3526 30 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 233
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 233 (accept_3_2 28 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 233 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 233 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 233 (accept_3_2 25 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 233
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 23 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 125 233 (accept_3_2 22 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 125 233 (Polychromatic418967fa.accept_16_5_13_9_1_2594 21 125 233 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 20 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 233 (accept_3_2 19 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 233 (Polychromatic418967fa.accept_7_4_6_2_1_451
  18 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 233
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 233 (accept_3_2 16 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 233 (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 233 (accept_3_2 13 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 233 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 125 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 233
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 233 (accept_3_2 10 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 233 (Polychromatic418967fa.accept_11_9_4_2_1_600 9 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 233 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 233 (accept_3_2 7 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 233 (Polychromatic418967fa.accept_11_6_4_2_1_599 6 125 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 233
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 233 (accept_3_2 4 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 233 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 125 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 233 (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 233 (accept_3_2 1 125 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 124 233 (Eq.refl Bool.true) (allA_of_3_0 110 124 233 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 123 233 (Eq.refl Bool.true) (allA_succ_of_accept 110 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2
  110 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 233 (accept_3_2
  109 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 233
  (Polychromatic418967fa.accept_19_13_9_5_1_8541 108 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 123 233 (Polychromatic418967fa.accept_19_12_9_5_1_8593 107 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 233 (accept_3_2 106 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 105 123
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 123 233 (accept_3_2 103 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 102 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 123 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 101 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 233 (accept_3_2 100 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 123 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 99 123
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 98 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 123 233 (accept_3_2 97 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 96 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 123 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 95 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 233 (accept_3_2 94 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 93 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 123 233 (accept_3_2 91 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 233 (accept_3_2 88 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 233 (Polychromatic418967fa.accept_15_12_3_8_1_5245 87 123 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 86 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 123 233 (accept_3_2 85 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 84 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 123 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 233 (accept_3_2 82 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 123 233 (accept_3_2 79 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 123 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 233 (accept_3_2 76 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 123 233 (accept_3_2 73 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 123 233 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 123 233 (Polychromatic418967fa.accept_15_11_3_8_1_750 71 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 233 (accept_3_2 70 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 123 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 233 (accept_3_2 67 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 123 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 233 (accept_3_2 64 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 233 (Polychromatic418967fa.accept_18_9_15_17_1_3497 63 123 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 233 (accept_3_2 61 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 123 233 (Polychromatic418967fa.accept_17_9_4_12_1_2958 60 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 123 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 233 (accept_3_2 58 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 233 (accept_3_2 55 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 123 233 (Polychromatic418967fa.accept_16_5_11_9_1_861 53 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 233 (accept_3_2 52 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 233 (Polychromatic418967fa.accept_19_13_9_5_1_8541 51 123
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 50 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 233 (accept_3_2 49 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 123 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 233 (accept_3_2 46 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 233 (accept_3_2 43 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 123 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 233 (accept_3_2 40 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 233 (accept_3_2 37 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 123 233 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 123 233 (Polychromatic418967fa.accept_15_5_3_8_1_748 35 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 233 (accept_3_2 34 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 123 233
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 233 (accept_3_2 31 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 123 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 233 (accept_3_2 28 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 233 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 233 (accept_3_2 25 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 123 233 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 233 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 233 (accept_3_2 22 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 233 (accept_3_2 19 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 233 (Polychromatic418967fa.accept_23_17_8_3_1_9095 17 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 233 (accept_3_2 16 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 233 (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 123
  233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 233 (accept_3_2 13 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 233 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 233 (accept_3_2 10 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 233 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 233
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 233 (accept_3_2 7 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 233 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 233 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 233 (accept_3_2 4 123 233 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 233 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 123 233 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 233
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 233 (accept_3_2 1 123 233 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  233)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_233_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


