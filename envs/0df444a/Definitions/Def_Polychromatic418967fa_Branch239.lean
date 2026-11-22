-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch239
-- name    : Polychromatic418967fa_Branch239
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:49.972826+00:00
-- url     : https://prove2.me/theorems/6deca1fe-abbc-475d-a32c-edb8c5d83fc4
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch239_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_239 : allB 239 239 :=
  allB_succ' 2 238 239 (Eq.refl Bool.true) (allA_of_3_0 2 238 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  237 239 (Eq.refl Bool.true) (allA_succ_of_accept 2 237 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 239 (accept_3_2 1 237 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 239))) (allB_succ' 4 236 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 236 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 236 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 239 (accept_3_2 1 236 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236 239)))) (allB_succ' 5 235 239 (Eq.refl Bool.true) (allA_of_3_0
  5 235 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 234 239 (Eq.refl Bool.true) (allA_succ_of_accept 5
  234 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 234 239 (accept_3_2 4 234 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 234 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 234 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 234 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 239 (accept_3_2 1 234 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234 239)))))) (allB_succ' 7 233 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 233 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 233 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 239 (accept_3_2 4 233 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  233 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 239 (accept_3_2 1 233 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233 239)))))))
  (allB_succ' 8 232 239 (Eq.refl Bool.true) (allA_of_3_0 8 232 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 231 239 (Eq.refl Bool.true) (allA_succ_of_accept 8 231 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 239 (accept_3_2 7 231 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648
  6 231 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 231 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 239 (accept_3_2 4 231 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  231 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 231 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 231 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 231 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 239 (accept_3_2 1 231 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 231 239))))))))) (allB_succ' 10 230 239 (Eq.refl Bool.true) (allA_succ_of_accept 9 230
  239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 230 239 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 230 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 239 (accept_3_2 7 230 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 230 239 (Polychromatic418967fa.accept_15_6_5_14_1_429 6 230 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  230 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 239 (accept_3_2 4 230
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 239 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 230 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 230 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 230 239 (accept_3_2 1 230 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  239)))))))))) (allB_succ' 11 229 239 (Eq.refl Bool.true) (allA_of_3_0 11 229 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 228 239 (Eq.refl Bool.true) (allA_succ_of_accept 11 228 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 239 (accept_3_2 10 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  228 239 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 228 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 228 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 239 (accept_3_2 7 228 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 228 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 239 (accept_3_2 4 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  228 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 228 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 228 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 228 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 239 (accept_3_2 1 228 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 228 239)))))))))))) (allB_succ' 13 227 239 (Eq.refl Bool.true) (allA_succ_of_accept 12
  227 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 227 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 239 (accept_3_2 10 227 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 227 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 239 (accept_3_2 7 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 227 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 239 (accept_3_2 4 227 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 227 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 239 (accept_3_2 1 227 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  239))))))))))))) (allB_succ' 14 226 239 (Eq.refl Bool.true) (allA_of_3_0 14 226 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 225 239 (Eq.refl Bool.true) (allA_succ_of_accept 14 225 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 239 (accept_3_2 13 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 239 (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 225 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 239 (accept_3_2 10 225 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 239 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 225 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 239 (accept_3_2 7 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 239 (Polychromatic418967fa.accept_16_5_1_15_1_3922 5 225 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 239 (accept_3_2 4 225 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 225 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 239 (accept_3_2 1 225 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  239))))))))))))))) (allB_succ' 16 224 239 (Eq.refl Bool.true) (allA_succ_of_accept 15 224 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 224 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 224 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 239 (accept_3_2 13 224 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 224 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 224 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 224 239 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 239 (accept_3_2 10
  224 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 224 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 224 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 239 (accept_3_2 7 224 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 224 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 224 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 5
  224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 239 (accept_3_2 4 224
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 239 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 239 (accept_3_2 1 224 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  239)))))))))))))))) (allB_succ' 17 223 239 (Eq.refl Bool.true) (allA_of_3_0 17 223 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 222 239 (Eq.refl Bool.true) (allA_succ_of_accept 17 222 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 222 239 (accept_3_2 16 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 222 239 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 222 239 (Polychromatic418967fa.accept_21_14_12_8_1_6833 14 222 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 239 (accept_3_2 13 222 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 222 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 222 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 239 (accept_3_2 10 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  222 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 222 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 222 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 239 (accept_3_2 7 222 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 222 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 222 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 239 (accept_3_2 4 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  222 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 222 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 222 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 222 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 239 (accept_3_2 1 222 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 222 239)))))))))))))))))) (allB_succ' 19 221 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 221 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 221 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 239 (accept_3_2 16 221 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 239 (Polychromatic418967fa.accept_10_5_1_9_1_791
  15 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 239 (accept_3_2 13 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 239 (Polychromatic418967fa.accept_22_11_1_19_1_14315 11 221 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 239 (accept_3_2 10 221 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 239 (Polychromatic418967fa.accept_27_9_5_23_1_1290 9 221
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 239
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 239 (accept_3_2 7 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 221 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 239 (accept_3_2 4 221 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 221 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 239 (accept_3_2 1 221 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  239))))))))))))))))))) (allB_succ' 20 220 239 (Eq.refl Bool.true) (allA_of_3_0 20 220 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 219 239 (Eq.refl Bool.true) (allA_succ_of_accept 20 219 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 239 (accept_3_2 19 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 239 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 219 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 239 (accept_3_2 16 219 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 219 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 239 (accept_3_2 13 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 219 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 239 (accept_3_2 10 219 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 239 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 219 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 239 (accept_3_2 7 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 239 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 219 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 239 (accept_3_2 4 219 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 219 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 239 (accept_3_2 1 219 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  239))))))))))))))))))))) (allB_succ' 22 218 239 (Eq.refl Bool.true) (allA_succ_of_accept 21 218 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 218 239 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 218 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 239 (accept_3_2 19 218 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 218 239 (Polychromatic418967fa.accept_24_18_2_23_1_5664 18 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 239 (accept_3_2 16 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 239 (accept_3_2 13 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 218 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 239
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 218 239 (accept_3_2 10 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  218 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 218 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 218 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 239 (accept_3_2 7 218 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 239 (accept_3_2 4 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 218 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 239 (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 239 (accept_3_2 1 218 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 239)))))))))))))))))))))) (allB_succ' 23 217 239 (Eq.refl Bool.true)
  (allA_of_3_0 23 217 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 216 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 216 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 239 (accept_3_2 22 216 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 239 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 239
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 239 (accept_3_2 19 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 216 239 (Polychromatic418967fa.accept_19_18_7_11_1_7552 18 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 216 239 (Polychromatic418967fa.accept_16_1_8_15_1_1945 17 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 239 (accept_3_2 16 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 216 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 216
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 239
  (Polychromatic418967fa.accept_13_1_8_5_1_2315 14 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 216 239 (accept_3_2 13 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 216 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 216 239 (Polychromatic418967fa.accept_25_11_16_14_1_9111 11 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 216 239 (accept_3_2 10 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 216 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 216 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 239
  (Polychromatic418967fa.accept_15_8_6_14_1_975 8 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 216 239 (accept_3_2 7 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  216 239 (Polychromatic418967fa.accept_17_6_12_1_1_7043 6 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 216 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 216 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 239 (accept_3_2 4 216 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 216 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 239 (accept_3_2 1 216 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  239)))))))))))))))))))))))) (allB_succ' 25 215 239 (Eq.refl Bool.true) (allA_succ_of_accept 24 215 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 215 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 239 (accept_3_2 22 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 215 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 215 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 239 (Polychromatic418967fa.accept_7_6_5_1_1_416
  20 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 239 (accept_3_2 19
  215 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 215 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 239 (accept_3_2 16 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 215 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 215 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  14 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 239 (accept_3_2 13
  215 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 239
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 215 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 239 (accept_3_2 10 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 215 239 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 215 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 239 (Polychromatic418967fa.accept_15_8_5_14_1_986
  8 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 239 (accept_3_2 7
  215 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 215 239 (Polychromatic418967fa.accept_19_5_6_11_1_6069 5 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 239 (accept_3_2 4 215 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 215 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 215 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  215 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 239 (accept_3_2 1 215
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 239))))))))))))))))))))))))) (allB_succ' 26 214 239
  (Eq.refl Bool.true) (allA_of_3_0 26 214 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 213 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 26 213 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 239 (accept_3_2 25 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 213 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 239 (accept_3_2 22 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 239 (accept_3_2 19 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 239 (accept_3_2 16 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 239 (accept_3_2 13 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 213 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 239 (accept_3_2 10 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 239 (accept_3_2 7 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 239 (accept_3_2 4 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 213 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 239 (accept_3_2 1 213 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 239))))))))))))))))))))))))))) (allB_succ' 28 212 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 27 212 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 212
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 239 (accept_3_2 25 212
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 212 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 212 239 (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 239 (accept_3_2 22 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 212 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 239 (Polychromatic418967fa.accept_7_6_2_1_1_214
  20 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 239 (accept_3_2 19
  212 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 212 239
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 212 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 239 (accept_3_2 16 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 212 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 239 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 239 (accept_3_2 13
  212 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 239
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 212 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 239 (accept_3_2 10 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 212 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 239 (Polychromatic418967fa.accept_14_8_2_1_1_1652
  8 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 239 (accept_3_2 7
  212 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 212 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 239 (accept_3_2 4 212 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 212 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  212 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 239 (accept_3_2 1 212
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212 239)))))))))))))))))))))))))))) (allB_succ' 29 211 239
  (Eq.refl Bool.true) (allA_of_3_0 29 211 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 210 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 239 (accept_3_2 28 210 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 239 (Polychromatic418967fa.accept_18_9_12_5_1_864 27 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 239 (accept_3_2 25 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 210 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 210 239 (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 239 (accept_3_2 22 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 210 239 (accept_3_2 19 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 210 239 (Polychromatic418967fa.accept_19_18_1_11_1_10478 18 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 239 (accept_3_2 16 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 210 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 239
  (Polychromatic418967fa.accept_23_14_3_9_1_14314 14 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 210 239 (accept_3_2 13 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 210 239 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 210 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 210 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 239 (accept_3_2 10 210 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 239 (accept_3_2 7 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  210 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 210 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 239 (accept_3_2 4 210 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 239 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 210 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 239 (accept_3_2 1 210 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  239)))))))))))))))))))))))))))))) (allB_succ' 31 209 239 (Eq.refl Bool.true) (allA_succ_of_accept 30 209 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 209 239 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 209 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 239 (accept_3_2 28 209 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 209 239 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 209 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 239 (accept_3_2 25 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 209 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 239 (accept_3_2 22 209 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 209 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 239
  (Polychromatic418967fa.accept_22_20_11_19_1_14313 20 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 209 239 (accept_3_2 19 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 209 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 209 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 239 (accept_3_2 16 209 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 239 (Polychromatic418967fa.accept_9_6_2_5_1_506
  15 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 239 (accept_3_2 13 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 239 (Polychromatic418967fa.accept_16_11_1_15_1_1123 11 209 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 239 (accept_3_2 10 209 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 209 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 239 (accept_3_2 7 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 209 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 239 (accept_3_2 4 209 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 209 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 239 (accept_3_2 1 209 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  239))))))))))))))))))))))))))))))) (allB_succ' 32 208 239 (Eq.refl Bool.true) (allA_of_3_0 32 208 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 207 239 (Eq.refl Bool.true) (allA_succ_of_accept 32 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 239 (accept_3_2 31 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 207 239 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 207 239 (Polychromatic418967fa.accept_24_5_15_23_1_5647 29 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 239 (accept_3_2 28 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 207 239 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 207
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 239 (accept_3_2 25 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 207 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 207 239 (Polychromatic418967fa.accept_17_6_3_1_1_7011 23 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 239 (accept_3_2 22 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 207 239 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 207
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 207 239 (accept_3_2 19 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 207 239 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 207 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 207 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 239 (accept_3_2 16 207 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 239 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 207 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 239 (accept_3_2 13 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 207 239 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 239 (accept_3_2 10 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 207
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 239 (accept_3_2 7 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 207 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 239 (accept_3_2 4 207 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 239 (accept_3_2 1 207 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  239))))))))))))))))))))))))))))))))) (allB_succ' 34 206 239 (Eq.refl Bool.true) (allA_succ_of_accept 33 206 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 206 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 206 239 (accept_3_2 31 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 206 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 206 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 206 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 239 (accept_3_2 28
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 206 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 239 (accept_3_2 25 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 206 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 206 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 23
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 239 (accept_3_2 22
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 206 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 239 (accept_3_2 19 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 206 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 206 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 206 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 239 (accept_3_2 16
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 206 239 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 239 (accept_3_2 13 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 206 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 206 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 239 (accept_3_2 10
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 206 239 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 239 (accept_3_2 7 206 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 206 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 206 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 239 (accept_3_2 4 206
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 239 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 239 (accept_3_2 1 206 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  239)))))))))))))))))))))))))))))))))) (allB_succ' 35 205 239 (Eq.refl Bool.true) (allA_of_3_0 35 205 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 204 239 (Eq.refl Bool.true) (allA_succ_of_accept 35 204 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 204 239 (accept_3_2 34 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 204 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 204 239 (Polychromatic418967fa.accept_24_8_12_23_1_14312 32 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 239 (accept_3_2 31 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 204 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 204 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 204 239 (accept_3_2 28 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 204 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 204 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 239 (accept_3_2 25 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 239 (Polychromatic418967fa.accept_16_8_12_15_1_2005 24 204 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 204 239
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 239 (accept_3_2 22 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 204 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 204 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 239 (accept_3_2 19 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 204 239 (accept_3_2 16 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 204 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 204 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 239 (accept_3_2 13 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 204 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 239 (accept_3_2 10 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  204 239 (Polychromatic418967fa.accept_14_9_8_1_1_2381 9 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 204 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 239 (accept_3_2 7 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 6 204 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 239
  (Polychromatic418967fa.accept_10_5_4_9_1_420 5 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 239 (accept_3_2 4 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  204 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 204 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 204 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 239 (accept_3_2 1 204 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 239)))))))))))))))))))))))))))))))))))) (allB_succ' 37 203 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 203 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 203 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 203
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 239 (accept_3_2 34 203
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 239
  (Polychromatic418967fa.accept_16_1_11_15_1_498 33 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 203 239 (Polychromatic418967fa.accept_17_15_16_1_1_7080 32 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 239 (accept_3_2 31 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 239 (Polychromatic418967fa.accept_20_10_3_19_1_2931 30 203 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 203 239
  (Polychromatic418967fa.accept_13_3_8_5_1_974 29 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 203 239 (accept_3_2 28 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 203 239 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 203 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 203 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 203 239 (accept_3_2 25 203 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 203 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 203
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 203 239
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 203 239 (accept_3_2 22 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 203 239 (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 203 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 203 239 (accept_3_2 19 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 203 239 (Polychromatic418967fa.accept_25_18_3_14_1_12625 18 203 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 203 239
  (Polychromatic418967fa.accept_16_1_11_15_1_498 17 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 203 239 (accept_3_2 16 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 203 239 (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 203 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 203 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 239 (accept_3_2 13 203 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 203 239
  (Polychromatic418967fa.accept_21_11_14_8_1_5256 11 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 203 239 (accept_3_2 10 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 203 239 (Polychromatic418967fa.accept_15_9_8_14_1_1699 9 203 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 239 (Polychromatic418967fa.accept_14_8_7_1_1_1615 8 203 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 239 (accept_3_2 7 203 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  6 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 203 239 (accept_3_2 4 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  203 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 203 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 203 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 239 (accept_3_2 1 203 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 239))))))))))))))))))))))))))))))))))))) (allB_succ' 38 202 239 (Eq.refl Bool.true)
  (allA_of_3_0 38 202 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 201 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 201 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 239 (accept_3_2 37 201 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 239 (accept_3_2 34 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 201 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 201 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 239 (accept_3_2 31 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 239 (accept_3_2 28 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 201 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 239 (accept_3_2 25 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 201 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 239
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 201 239 (accept_3_2 22 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 201 239 (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 201 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 239 (accept_3_2 19 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 239 (accept_3_2 16 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 201 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 239 (accept_3_2 13 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 12 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 239 (accept_3_2 10 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 239 (accept_3_2 7 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 239 (accept_3_2 4 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 201 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 239 (accept_3_2 1 201 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 239))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 200 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 38
  200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 200 239 (accept_3_2 37
  200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 200 239
  (Polychromatic418967fa.accept_15_6_5_14_1_429 36 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 200 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 200 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 239 (accept_3_2 34 200 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 239 (Polychromatic418967fa.accept_15_2_5_14_1_61
  32 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 200 239 (accept_3_2 31
  200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 200 239
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 200 239 (Polychromatic418967fa.accept_17_12_13_1_1_4478 29 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 239 (accept_3_2 28 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 239 (accept_3_2 25 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 239 (accept_3_2 22 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 239
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 20 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 239 (accept_3_2 19 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 239 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 239 (accept_3_2 16 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 239 (accept_3_2 13 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 239 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 239 (accept_3_2 10 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 239 (accept_3_2 7 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 239 (accept_3_2 4 200 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 239 (accept_3_2 1 200 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  239)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 199 239 (Eq.refl Bool.true) (allA_of_3_0 41 199 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 198 239 (Eq.refl Bool.true) (allA_succ_of_accept 41 198 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 198 239 (accept_3_2 40 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 198 239 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 198 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 239 (accept_3_2 37 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 198 239 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 198 239
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 198 239 (accept_3_2 34 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 198 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 198 239 (Polychromatic418967fa.accept_13_6_3_5_1_3167 32 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 198 239 (accept_3_2 31 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 198 239 (Polychromatic418967fa.accept_27_3_9_23_1_14311 30 198
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 198 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 198 239 (accept_3_2 28 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 198 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 198 239 (Polychromatic418967fa.accept_15_11_3_14_1_971 26 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 239 (accept_3_2 25 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 198 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 198 239
  (Polychromatic418967fa.accept_16_7_6_15_1_495 23 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 239 (accept_3_2 22 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 198 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 198 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 239 (accept_3_2 19 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 239 (Polychromatic418967fa.accept_19_18_8_11_1_7663 18 198 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 198 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 239 (accept_3_2 16 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 239 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 239 (accept_3_2 13 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 239 (Polychromatic418967fa.accept_19_12_8_11_1_7554 12 198
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 239
  (Polychromatic418967fa.accept_10_1_8_9_1_787 11 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 239 (accept_3_2 10 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  198 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 198 239 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 239 (accept_3_2 7 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 198 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 239 (accept_3_2 4 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  198 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 198 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 198 239 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 239 (accept_3_2 1 198 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198 239)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 197 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 197 239
  (Polychromatic418967fa.accept_17_7_10_1_1_4488 41 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 197 239 (accept_3_2 40 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 197 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 197 239 (accept_3_2 37 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 197 239 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 197 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 197 239
  (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 197 239 (accept_3_2 34 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 197 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 197 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 197 239 (accept_3_2 31 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 197 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 197 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 197 239 (accept_3_2 28 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 197 239 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 197 239 (accept_3_2 25 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 197 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 197 239
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 197 239 (accept_3_2 22 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 197 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 197 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 239 (accept_3_2 19 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 239
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 197 239 (accept_3_2 16 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 197 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 239 (accept_3_2 13 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 239 (accept_3_2 10 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 239 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 239 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 239 (accept_3_2 7 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 239
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 239 (accept_3_2 4 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 197 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 239 (accept_3_2 1 197 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 239))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 196 239 (Eq.refl
  Bool.true) (allA_of_3_0 44 196 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 195 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 195 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 239 (accept_3_2 43 195 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 195 239 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 195 239
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 239 (accept_3_2 40 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 195 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 239 (accept_3_2 37 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 195 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 195 239 (accept_3_2 34 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 195 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 239 (accept_3_2 31 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 195 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 239 (accept_3_2 28 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 195 239 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 239 (accept_3_2 25 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 195 239 (accept_3_2 22 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 195 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 239 (accept_3_2 19 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 239 (Polychromatic418967fa.accept_16_2_3_15_1_6309 18 195 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 239 (accept_3_2 16 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 239 (Polychromatic418967fa.accept_19_15_5_11_1_4719 15 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 239 (accept_3_2 13 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 239 (accept_3_2 10 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 239 (accept_3_2 7 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 6 195 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 239 (accept_3_2 4 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 195 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 239 (accept_3_2 1 195 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 239))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 194 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 239 (Polychromatic418967fa.accept_12_8_2_11_1_246
  44 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 194 239 (accept_3_2 43
  194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 194 239
  (Polychromatic418967fa.accept_17_8_7_1_1_4521 42 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 194 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 239 (accept_3_2 40 194 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 194 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 194 239 (accept_3_2 37
  194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 194 239
  (Polychromatic418967fa.accept_19_17_4_11_1_4731 36 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 239 (accept_3_2 34 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 194 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 239 (accept_3_2 31 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 239 (Polychromatic418967fa.accept_13_4_12_5_1_476 30 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 239 (accept_3_2 28 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 239
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 239 (accept_3_2 25 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 239 (accept_3_2 22 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 239 (accept_3_2 19 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 239 (accept_3_2 16 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 239
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 194 239 (accept_3_2 13 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 194 239 (Polychromatic418967fa.accept_16_12_2_15_1_490 12 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 194 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 239 (accept_3_2 10 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 239
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 239 (accept_3_2 7 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 239 (accept_3_2 4 194 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 239
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 239 (accept_3_2 1 194 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  239)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 193 239 (Eq.refl Bool.true) (allA_of_3_0 47 193 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 192 239 (Eq.refl Bool.true) (allA_succ_of_accept 47 192 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 192 239 (accept_3_2 46 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 192 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 192 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 192 239 (accept_3_2 43 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 192 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 192 239
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 192 239 (accept_3_2 40 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 192 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 192 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 192 239 (accept_3_2 37 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 192 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 192 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 192 239 (accept_3_2 34 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 192 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 192 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 239 (accept_3_2 31 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 192 239 (accept_3_2 28 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 192 239 (Polychromatic418967fa.accept_10_7_2_9_1_775 27 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 192 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 239 (accept_3_2 25 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 239 (accept_3_2 22 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 192 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 21 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 192 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 239 (accept_3_2 19 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 239 (accept_3_2 16 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 192 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 192 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 239 (accept_3_2 13 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 192 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 239 (accept_3_2 10 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  192 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 192 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 239 (accept_3_2 7 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 192 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 239 (accept_3_2 4 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 192 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 239 (accept_3_2 1 192 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192 239)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 191 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 191 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 239
  (Polychromatic418967fa.accept_19_9_1_11_1_7643 47 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 239 (accept_3_2 46 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 239 (accept_3_2 43 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 239 (accept_3_2 40 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 239 (accept_3_2 37 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 239 (Polychromatic418967fa.accept_14_8_9_1_1_3313 36 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 239 (accept_3_2 34 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 239 (accept_3_2 31 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 191 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 239
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 239 (accept_3_2 28 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 239 (accept_3_2 25 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 239
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 239 (accept_3_2 22 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 239 (accept_3_2 19 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 239 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 239 (accept_3_2 16 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 239 (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 239 (accept_3_2 13 191 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 191 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 239
  (Polychromatic418967fa.accept_23_11_7_9_1_14310 11 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 239 (accept_3_2 10 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 239 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 191 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 191 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 239 (accept_3_2 7 191 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6
  191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 239 (accept_3_2 4 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 191 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 239 (accept_3_2 1 191 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 239))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 190 239
  (Eq.refl Bool.true) (allA_of_3_0 50 190 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 189 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 189 239 (accept_3_2 49 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 189 239 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 189 239
  (Polychromatic418967fa.accept_17_13_2_1_1_4483 47 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 189 239 (accept_3_2 46 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 189 239 (Polychromatic418967fa.accept_19_7_18_11_1_464 45 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 189 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 189 239 (accept_3_2 43 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 189 239
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 189 239 (accept_3_2 40 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 189 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 189 239 (accept_3_2 37 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 189 239 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 189 239
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 189 239 (accept_3_2 34 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 189 239 (Polychromatic418967fa.accept_17_16_2_1_1_4492 33 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 189 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 239 (accept_3_2 31 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 239
  (Polychromatic418967fa.accept_19_10_18_11_1_10502 29 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 189 239 (accept_3_2 28 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 189 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 189 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 239 (accept_3_2 25 189 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 239
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 239 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 189 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 239 (accept_3_2 22 189 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 239 (accept_3_2 19 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 239 (Polychromatic418967fa.accept_19_17_18_11_1_2215 17 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 239 (accept_3_2 16 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 189
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 239 (accept_3_2 13 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 239 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 239 (accept_3_2 10 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 239 (Polychromatic418967fa.accept_26_9_7_5_1_14309 9 189
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 239 (accept_3_2 7 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 239 (accept_3_2 4 189 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 189 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 239 (accept_3_2 1 189 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  239))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 188 239 (Eq.refl Bool.true) (allA_succ_of_accept
  51 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 188 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 188 239 (accept_3_2 49 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 188 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 188 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 188 239 (accept_3_2 46 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 188 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 188 239 (accept_3_2 43 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 188 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 188 239
  (Polychromatic418967fa.accept_10_1_8_9_1_787 41 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 188 239 (accept_3_2 40 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 188 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 188 239 (accept_3_2 37 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 188 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 188 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 188 239 (accept_3_2 34 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 188 239 (Polychromatic418967fa.accept_18_14_8_5_1_860 32 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 188 239 (accept_3_2 31 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 188 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 188 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 188 239 (accept_3_2 28 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 188 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 239 (accept_3_2 25 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 188 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 188 239 (accept_3_2 22 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 188 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 239 (accept_3_2 19 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 239 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 239
  (Polychromatic418967fa.accept_10_7_8_9_1_785 17 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 239 (accept_3_2 16 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 14 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 239 (accept_3_2 13 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 239 (accept_3_2 10 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 239 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 239 (accept_3_2 7 188 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 188 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 239 (accept_3_2 4 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 239 (accept_3_2 1 188 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 239)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 187 239
  (Eq.refl Bool.true) (allA_of_3_0 53 187 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 186 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 186 239 (accept_3_2 52 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 186 239 (Polychromatic418967fa.accept_13_12_4_5_1_1637 51 186 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 186 239
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 186 239 (accept_3_2 49 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 186 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 186 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 186 239 (accept_3_2 46 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 186 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 186 239 (accept_3_2 43 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 186 239 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 186 239 (accept_3_2 40 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 186 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 186 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 186 239 (accept_3_2 37 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 186 239 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 186 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 239 (accept_3_2 34 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 239
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 32 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 186 239 (accept_3_2 31 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 186 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 239 (accept_3_2 28 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 239 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 239 (accept_3_2 25 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 186 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 239 (accept_3_2 22 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 239 (accept_3_2 19 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 239 (Polychromatic418967fa.accept_35_18_11_29_1_14308 18 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 239 (accept_3_2 16 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 186
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 239
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 239 (accept_3_2 13 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 186 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 186 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 239 (accept_3_2 10 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 239 (accept_3_2 7 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 239 (Polychromatic418967fa.accept_13_6_4_5_1_2330 6 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 239 (accept_3_2 4 186 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 239 (accept_3_2 1 186 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 185 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 185 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 185 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 185 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 185 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 239 (accept_3_2 52 185 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 51
  185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 239 (accept_3_2 49 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 239 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 239 (accept_3_2 46 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 239 (Polychromatic418967fa.accept_13_6_3_5_1_3167 45 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 239 (accept_3_2 43 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 239 (accept_3_2 40 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 185 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 239 (accept_3_2 37 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 185 239 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 239 (accept_3_2 34 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 185 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 239 (accept_3_2 31 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 239 (Polychromatic418967fa.accept_17_12_15_1_1_5798 29 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 239 (accept_3_2 28 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 239 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 185
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 239 (accept_3_2 25 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 239 (accept_3_2 22 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 239
  (Polychromatic418967fa.accept_17_3_15_1_1_3348 20 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 239 (accept_3_2 19 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 239 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 239 (accept_3_2 16 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 239 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 185
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 239 (accept_3_2 13 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 239 (accept_3_2 10 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 239
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 239 (accept_3_2 7 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 239 (accept_3_2 4 185 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 239 (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 185 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 239 (accept_3_2 1 185 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 184 239 (Eq.refl Bool.true) (allA_of_3_0 56
  184 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 183 239 (Eq.refl Bool.true) (allA_succ_of_accept 56
  183 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 183 239 (accept_3_2 55 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 183 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 54 183 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 239 (accept_3_2 52 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240
  51 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 239 (accept_3_2 49 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 183 239 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 239 (accept_3_2 46 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 183 239 (accept_3_2 43 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 183 239 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 239 (accept_3_2 40 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 239 (Polychromatic418967fa.accept_19_1_12_11_1_1245 39 183
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 239 (accept_3_2 37 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 239 (accept_3_2 34 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 239 (accept_3_2 31 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 239 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 239 (accept_3_2 28 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 239 (Polychromatic418967fa.accept_16_11_7_15_1_1998 27 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 239 (accept_3_2 25 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 239 (Polychromatic418967fa.accept_19_4_12_11_1_10461 23 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 239 (accept_3_2 22 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 183
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 239 (accept_3_2 19 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 239 (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 239 (accept_3_2 16 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 239 (accept_3_2 13 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 239 (accept_3_2 10 183 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 239 (accept_3_2 7 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 239 (Polychromatic418967fa.accept_19_5_12_11_1_10460 5 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 239 (accept_3_2 4 183 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 239 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 183 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 239 (accept_3_2 1 183 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 182 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 182 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 182 239 (Polychromatic418967fa.accept_12_8_2_11_1_246 56 182
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 182 239 (accept_3_2 55 182
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 182 239
  (Polychromatic418967fa.accept_21_12_14_8_1_5258 54 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 182 239 (accept_3_2 52 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 182 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 182 239
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 50 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 182 239 (accept_3_2 49 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 182 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 182 239 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 182 239 (accept_3_2 46 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 182 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 182 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 182 239 (accept_3_2 43 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 182 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 182 239 (accept_3_2 40 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 182 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 182 239
  (Polychromatic418967fa.accept_21_17_14_8_1_11452 38 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 182 239 (accept_3_2 37 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 182 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 182 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 182 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 182 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 239 (accept_3_2 34 182 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 239 (accept_3_2 31 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 239 (accept_3_2 28 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 182 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 182 239 (accept_3_2 25 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 182 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 182 239 (Polychromatic418967fa.accept_16_7_6_15_1_495 23 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 239 (accept_3_2 22 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 182 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 182 239 (accept_3_2 19 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 239 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 239 (accept_3_2 16 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 239
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 239 (accept_3_2 13 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 239 (accept_3_2 10 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 239 (accept_3_2 7 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 239 (accept_3_2 4 182 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 182 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 239
  (Polychromatic418967fa.accept_21_2_14_8_1_6834 2 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 239 (accept_3_2 1 182 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 181 239 (Eq.refl Bool.true) (allA_of_3_0
  59 181 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 180 239 (Eq.refl Bool.true) (allA_succ_of_accept 59
  180 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 180 239 (accept_3_2 58 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 180 239 (Polychromatic418967fa.accept_21_15_12_8_1_5275 57 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 180 239 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  56 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 180 239 (accept_3_2 55
  180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 180 239
  (Polychromatic418967fa.accept_24_6_12_23_1_14307 54 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 180 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 180 239 (accept_3_2 52 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 180 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 180 239
  (Polychromatic418967fa.accept_23_4_19_9_1_14306 50 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 180 239 (accept_3_2 49 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 180 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 180 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 180 239 (Polychromatic418967fa.accept_21_5_12_8_1_6807 47 180
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 180 239 (accept_3_2 46 180
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 180 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 180 239 (Polychromatic418967fa.accept_16_12_4_15_1_5091 44 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 180 239 (accept_3_2 43 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 239 (Polychromatic418967fa.accept_13_3_11_5_1_2348 42 180 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 180 239 (accept_3_2 40 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 180 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 180 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 38 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 180 239 (accept_3_2 37 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 239 (Polychromatic418967fa.accept_19_17_9_11_1_6057 36 180 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 180 239 (accept_3_2 34 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 180 239 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 180 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 239 (accept_3_2 31 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 239 (Polychromatic418967fa.accept_16_14_4_15_1_3944 30 180 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 239
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 180 239 (accept_3_2 28 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 180 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 180 239 (Polychromatic418967fa.accept_17_9_10_1_1_3345 26 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 239 (accept_3_2 25 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 180 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 239
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 180 239 (accept_3_2 22 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 180 239 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 180 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 239 (accept_3_2 19 180 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 239 (accept_3_2 16 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 180 239 (Polychromatic418967fa.accept_19_15_9_11_1_7514 15 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 180 239 (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 239 (accept_3_2 13 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 239 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 180
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 239 (accept_3_2 10 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  180 239 (Polychromatic418967fa.accept_17_9_10_1_1_3345 9 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 180 239 (Polychromatic418967fa.accept_16_8_4_15_1_2941 8 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 239 (accept_3_2 7 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 180 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 239
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 239 (accept_3_2 4 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 239 (Polychromatic418967fa.accept_19_2_9_11_1_7515 2 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 239 (accept_3_2 1 180 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 179 239 (Eq.refl Bool.true) (allA_succ_of_accept 60 179 239 (Polychromatic418967fa.accept_8_4_3_7_1_491
  60 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 179 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 179 239 (accept_3_2 58 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 179 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 179 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 179 239 (accept_3_2 55 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 179 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 239
  (Polychromatic418967fa.accept_24_5_11_23_1_7419 53 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 179 239 (accept_3_2 52 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 179 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 179 239 (Polychromatic418967fa.accept_11_6_3_8_1_843 50 179
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 239 (accept_3_2 49 179
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 179 239
  (Polychromatic418967fa.accept_9_3_8_5_1_65 48 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 179 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 239 (accept_3_2 46 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 179 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 179 239 (Polychromatic418967fa.accept_8_4_3_7_1_491
  44 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 239 (accept_3_2 43
  179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 179 239
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 179 239 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 239 (accept_3_2 40 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 179 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 38
  179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 239 (accept_3_2 37
  179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 239
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 179 239 (Polychromatic418967fa.accept_19_16_8_11_1_6080 35 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 239 (accept_3_2 34 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 239
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 32 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 239 (accept_3_2 31 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 239 (accept_3_2 28 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 239 (accept_3_2 25 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 239 (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 239 (accept_3_2 22 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 179 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 239
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 239 (accept_3_2 19 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 239 (Polychromatic418967fa.accept_14_4_11_1_1_940 18 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 239 (accept_3_2 16 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 239
  (Polychromatic418967fa.accept_21_14_11_8_1_5272 14 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 179 239 (accept_3_2 13 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 179 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 179 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 239 (accept_3_2 10 179 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 239 (Polychromatic418967fa.accept_19_9_8_11_1_6072
  9 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 239
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 239 (accept_3_2 7 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 239 (accept_3_2 4 179 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 179 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 239 (accept_3_2 1 179 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 178 239 (Eq.refl Bool.true)
  (allA_of_3_0 62 178 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 177 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 177 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 177 239 (accept_3_2 61 177 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 177 239 (Polychromatic418967fa.accept_18_6_15_5_1_6563 60 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 177 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 177 239 (accept_3_2 58 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 177 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 177 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 177 239 (accept_3_2 55 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 177 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 177 239 (accept_3_2 52 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 177 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 177 239 (accept_3_2 49 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 177 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 177 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 177 239 (accept_3_2 46 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 177 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 177 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 239 (accept_3_2 43 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 177 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 239 (accept_3_2 40 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 239 (accept_3_2 37 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 239 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 177 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 239 (accept_3_2 34 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 239 (Polychromatic418967fa.accept_19_14_6_11_1_7599 33 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 239 (accept_3_2 31 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 239 (accept_3_2 28 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 239 (accept_3_2 25 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 239
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 239 (accept_3_2 22 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 239 (accept_3_2 19 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 239 (accept_3_2 16 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 239 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 239 (accept_3_2 13 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 239 (accept_3_2 10 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 239 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 239 (accept_3_2 7 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 239
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 5 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 239 (accept_3_2 4 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 177 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 239 (accept_3_2 1 177 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  176 239 (Eq.refl Bool.true) (allA_succ_of_accept 63 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 176 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 176 239 (accept_3_2 61 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 176 239 (Polychromatic418967fa.accept_23_14_15_9_1_14305 60 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 176 239 (Polychromatic418967fa.accept_25_9_1_14_1_14304 59 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 176 239 (accept_3_2 58 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 57
  176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 176 239
  (Polychromatic418967fa.accept_17_5_6_1_1_5735 56 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 176 239 (accept_3_2 55 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 176 239 (Polychromatic418967fa.accept_13_2_7_5_1_3189 54 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 176 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 53 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 176 239 (accept_3_2 52 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 176 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 176 239 (accept_3_2 49 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 176 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 48 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 176 239 (Polychromatic418967fa.accept_18_11_14_5_1_3951 47 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 176 239 (accept_3_2 46 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 176 239
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 44 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 176 239 (accept_3_2 43 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 176 239 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 176 239 (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 176 239 (accept_3_2 40 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 176 239 (accept_3_2 37 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 176 239 (Polychromatic418967fa.accept_17_2_6_1_1_8357 36 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 239 (accept_3_2 34 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 239
  (Polychromatic418967fa.accept_19_13_5_11_1_7653 32 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 176 239 (accept_3_2 31 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 176 239 (Polychromatic418967fa.accept_14_2_8_1_1_1647 30 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 176 239 (Polychromatic418967fa.accept_17_12_6_1_1_4517 29 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 239 (accept_3_2 28 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 176 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 176 239 (accept_3_2 25 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 176 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 176 239
  (Polychromatic418967fa.accept_10_3_6_9_1_779 23 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 176 239 (accept_3_2 22 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 176 239 (Polychromatic418967fa.accept_17_3_6_1_1_8382 20 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 239 (accept_3_2 19 176 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 239
  (Polychromatic418967fa.accept_19_17_5_11_1_7509 17 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 176 239 (accept_3_2 16 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 239 (accept_3_2 13 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 239
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 176 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 239 (accept_3_2 10 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 239 (Polychromatic418967fa.accept_18_8_14_5_1_2778
  8 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 239 (accept_3_2 7
  176 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 239
  (Polychromatic418967fa.accept_19_6_5_11_1_6067 6 176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 176 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 5 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 239 (accept_3_2 4 176 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 176 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 2
  176 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 239 (accept_3_2 1 176
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 175 239 (Eq.refl Bool.true)
  (allA_of_3_0 65 175 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 174 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 174 239 (accept_3_2 64 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 174 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 174 239 (Polychromatic418967fa.accept_9_8_3_5_1_241
  62 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 174 239 (accept_3_2 61
  174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 174 239
  (Polychromatic418967fa.accept_9_6_3_5_1_240 60 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 174 239 (Polychromatic418967fa.accept_17_8_4_1_1_5730 59 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 174 239 (accept_3_2 58 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 174 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 56
  174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 174 239 (accept_3_2 55
  174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 174 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 174 239 (accept_3_2 52 174 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 174 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 174 239
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 174 239 (accept_3_2 49 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 174 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 174 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 174 239 (accept_3_2 46 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 174 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 174 239 (accept_3_2 43 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 174 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 239 (accept_3_2 40 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 239 (Polychromatic418967fa.accept_16_7_14_15_1_2932 39 174 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 174 239 (accept_3_2 37 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 174 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 174 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 239 (accept_3_2 34 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 239
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 174 239 (accept_3_2 31 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 174 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 239 (accept_3_2 28 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 174 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 239 (accept_3_2 25 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 174 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 174 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 239 (accept_3_2 22 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 20 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 239 (accept_3_2 19 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 174 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 239 (accept_3_2 16 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 239
  (Polychromatic418967fa.accept_17_14_4_1_1_3341 14 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 174 239 (accept_3_2 13 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 174 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 174 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 239 (accept_3_2 10 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 239 (accept_3_2 7 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  174 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 174 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 239 (accept_3_2 4 174 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 3 174 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 239 (accept_3_2 1 174 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 173 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 173 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 173 239 (Polychromatic418967fa.accept_15_5_8_14_1_432 65 173
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 239 (accept_3_2 64 173
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 239
  (Polychromatic418967fa.accept_24_15_5_23_1_9282 63 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 173 239 (accept_3_2 61 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 173 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 173 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 59 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 173 239 (accept_3_2 58 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 173 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 173 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 56 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 173 239 (accept_3_2 55 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 173 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 173 239 (accept_3_2 52 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 173 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 173 239 (accept_3_2 49 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 173 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 239
  (Polychromatic418967fa.accept_19_9_2_11_1_7581 47 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 239 (accept_3_2 46 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 173 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 239 (accept_3_2 43 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 239 (accept_3_2 40 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 239 (accept_3_2 37 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 239 (accept_3_2 34 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 239 (accept_3_2 31 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 239
  (Polychromatic418967fa.accept_19_10_2_11_1_11720 29 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 173 239 (accept_3_2 28 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 173 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 173 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 239 (accept_3_2 25 173 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24
  173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 239
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 239 (accept_3_2 22 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 239 (accept_3_2 19 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 239 (accept_3_2 16 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 239 (accept_3_2 13 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 173 239 (accept_3_2 10 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  173 239 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 173 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 239 (accept_3_2 7 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 5 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 239 (accept_3_2 4 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 173 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 239 (accept_3_2 1 173 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 172 239 (Eq.refl Bool.true) (allA_of_3_0 68 172 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 171 239
  (Eq.refl Bool.true) (allA_succ_of_accept 68 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 171 239 (accept_3_2 67 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 171 239 (Polychromatic418967fa.accept_18_12_9_5_1_2771 66 171
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 171 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 171 239 (accept_3_2 64 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 171 239 (Polychromatic418967fa.accept_25_13_21_14_1_14303 63 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 171 239 (accept_3_2 61 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 171 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 171 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 239
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 59 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 171 239 (accept_3_2 58 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 171 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 239 (accept_3_2 55 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 171 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 239 (accept_3_2 52 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 239 (accept_3_2 49 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 239 (Polychromatic418967fa.accept_10_8_1_9_1_413 48 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 239 (accept_3_2 46 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 239 (accept_3_2 43 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 239
  (Polychromatic418967fa.accept_23_18_10_9_1_14302 41 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 171 239 (accept_3_2 40 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 171 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 171 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 171 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 239 (accept_3_2 37 171 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 239 (Polychromatic418967fa.accept_8_4_3_7_1_491
  36 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 35 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 239 (accept_3_2 34 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 239 (accept_3_2 31 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 239
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 239 (accept_3_2 28 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 239 (Polychromatic418967fa.accept_21_6_3_8_1_9928 27 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 239 (accept_3_2 25 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 171 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 239 (accept_3_2 22 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 239 (accept_3_2 19 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 239
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 239 (accept_3_2 16 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 239 (accept_3_2 13 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 239 (accept_3_2 10 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 239 (accept_3_2 7 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 239 (Polychromatic418967fa.accept_21_6_3_8_1_9928 6 171 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 239 (accept_3_2 4 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 171 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 239 (accept_3_2 1 171 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 170 239 (Eq.refl Bool.true) (allA_succ_of_accept 69 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 170 239
  (Polychromatic418967fa.accept_11_2_5_8_1_470 68 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 170 239 (accept_3_2 67 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 170 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 170 239 (accept_3_2 64 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 170 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 170 239 (accept_3_2 61 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 170 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 170 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 170 239 (accept_3_2 58 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 170 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 170 239 (accept_3_2 55 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 170 239 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 170 239 (accept_3_2 52 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 170 239
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 170 239 (accept_3_2 49 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 170 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 170 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 170 239 (accept_3_2 46 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 170 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 170 239 (accept_3_2 43 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 170 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 170 239 (accept_3_2 40 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 170 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 170 239 (accept_3_2 37 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 170 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 170 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 170 239 (accept_3_2 34 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 170 239 (accept_3_2 31 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 170 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 239 (accept_3_2 28 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 239
  (Polychromatic418967fa.accept_19_7_18_11_1_464 26 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 170 239 (accept_3_2 25 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 170 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 170 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 239 (accept_3_2 22 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 170 239 (accept_3_2 19 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 170 239 (Polychromatic418967fa.accept_24_18_2_23_1_5664 18 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 239 (accept_3_2 16 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 239
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 170 239 (accept_3_2 13 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 239 (accept_3_2 10 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 239 (accept_3_2 7 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 239 (accept_3_2 4 170 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 170 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 239 (accept_3_2 1 170 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 169 239 (Eq.refl Bool.true)
  (allA_of_3_0 71 169 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 168 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 168 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 168 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 168 239 (accept_3_2 70 168 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 168 239 (Polychromatic418967fa.accept_13_4_12_5_1_476 69 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 168 239
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 68 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 168 239 (accept_3_2 67 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 168 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 168 239 (accept_3_2 64 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 168 239 (Polychromatic418967fa.accept_17_12_15_1_1_5798 63 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 168 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 168 239 (accept_3_2 61 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 168 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 168 239 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 168 239 (accept_3_2 58 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 168 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 168 239 (accept_3_2 55 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 168 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 168 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 239 (accept_3_2 52 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 168 239 (Polychromatic418967fa.accept_10_1_8_9_1_787 51 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 239
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 168 239 (accept_3_2 49 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 168 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 239 (accept_3_2 46 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 168 239 (accept_3_2 43 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 168 239 (Polychromatic418967fa.accept_19_4_16_11_1_6046 42 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 168 239 (Polychromatic418967fa.accept_10_1_8_9_1_787 41 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 168 239 (accept_3_2 40 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 168 239 (accept_3_2 37 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 168 239 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 168 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 239 (accept_3_2 34 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 168 239 (Polychromatic418967fa.accept_13_7_12_5_1_1603 33 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 239
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 168 239 (accept_3_2 31 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 168 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 239 (accept_3_2 28 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 168 239 (Polychromatic418967fa.accept_10_7_8_9_1_785 27 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 168 239 (accept_3_2 25 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 168 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 24 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 168 239 (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 239 (accept_3_2 22 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 168 239 (accept_3_2 19 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 168 239 (Polychromatic418967fa.accept_26_18_12_5_1_10790 18 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 239 (accept_3_2 16 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 239 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 168
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 239
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 168 239 (accept_3_2 13 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 168 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 239 (accept_3_2 10 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 239 (Polychromatic418967fa.accept_16_9_8_15_1_5095 9 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 168 239 (accept_3_2 7 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  168 239 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 168 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 239 (accept_3_2 4 168 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 239 (accept_3_2 1 168 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 167 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 167 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 167 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 167 239 (accept_3_2 70 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 167 239
  (Polychromatic418967fa.accept_27_15_5_23_1_14301 69 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 239 (accept_3_2 67 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 239 (Polychromatic418967fa.accept_19_9_15_11_1_7687 66 167 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 239 (accept_3_2 64 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 62 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 239 (accept_3_2 61 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 239
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 239 (accept_3_2 58 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 239 (Polychromatic418967fa.accept_15_12_2_14_1_5659 57 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 239 (Polychromatic418967fa.accept_16_8_7_15_1_6339 56 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 239 (accept_3_2 55 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 167 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 239
  (Polychromatic418967fa.accept_21_11_20_8_1_8403 53 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 167 239 (accept_3_2 52 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 167 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 167 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 239 (Polychromatic418967fa.accept_15_5_2_14_1_1693 50 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 239 (accept_3_2 49 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 239
  (Polychromatic418967fa.accept_10_8_7_9_1_425 48 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 167 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 239 (accept_3_2 46 167 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 167 239 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 239 (accept_3_2 43 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 42 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 239 (Polychromatic418967fa.accept_23_18_6_9_1_14300 41 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 239 (accept_3_2 40 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 239 (Polychromatic418967fa.accept_19_1_15_11_1_4712 39 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 239
  (Polychromatic418967fa.accept_10_8_7_9_1_425 38 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 239 (accept_3_2 37 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 239 (Polychromatic418967fa.accept_27_9_5_23_1_1290 36 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 239 (accept_3_2 34 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 167 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 239
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 239 (accept_3_2 31 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 239 (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 239 (accept_3_2 28 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 239 (accept_3_2 25 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 239 (Polychromatic418967fa.accept_16_8_7_15_1_6339 24 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 239 (accept_3_2 22 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 21 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 239
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 239 (accept_3_2 19 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 239 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 239 (Polychromatic418967fa.accept_20_17_7_19_1_13006 17 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 239 (accept_3_2 16 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 239 (Polychromatic418967fa.accept_23_15_6_9_1_14299 15 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 239
  (Polychromatic418967fa.accept_16_14_7_15_1_3947 14 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 167 239 (accept_3_2 13 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 239 (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 239 (accept_3_2 10 167
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 239 (Polychromatic418967fa.accept_7_2_6_1_1_73
  9 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 239
  (Polychromatic418967fa.accept_10_8_7_9_1_425 8 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 239 (accept_3_2 7 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 239 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 239 (accept_3_2 4 167 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 239 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 167 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 239 (accept_3_2 1 167 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 166 239 (Eq.refl
  Bool.true) (allA_of_3_0 74 166 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 165 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 74 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 165 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 239 (accept_3_2 73 165 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 165 239 (Polychromatic418967fa.accept_21_9_18_8_1_11475 72 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 239 (accept_3_2 70 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 165 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 239 (accept_3_2 67 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 239 (accept_3_2 64 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 165 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 239 (accept_3_2 61 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 239 (accept_3_2 58 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 239 (Polychromatic418967fa.accept_17_6_12_1_1_7043 57 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 239 (accept_3_2 55 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 239 (accept_3_2 52 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 239 (accept_3_2 49 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 239 (Polychromatic418967fa.accept_23_2_4_9_1_14298 48 165 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 239 (accept_3_2 46 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 239 (accept_3_2 43 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 239
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 239 (accept_3_2 40 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 239 (accept_3_2 37 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 239 (accept_3_2 34 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 239 (accept_3_2 31 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 239 (accept_3_2 28 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 239 (accept_3_2 25 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 239
  (Polychromatic418967fa.accept_17_6_12_1_1_7043 23 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 239 (accept_3_2 22 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 239 (accept_3_2 19 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 239 (accept_3_2 16 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 239 (accept_3_2 13 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 239 (accept_3_2 10 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 239 (Polychromatic418967fa.accept_21_9_18_8_1_11475 9 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 239 (accept_3_2 7 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 239 (accept_3_2 4 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 165 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 239 (accept_3_2 1 165 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 164 239 (Eq.refl Bool.true) (allA_succ_of_accept 75 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32
  75 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 164 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 164 239 (accept_3_2 73 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 164 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 164 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 164 239 (accept_3_2 70 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 164 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 164 239 (accept_3_2 67 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 164 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 164 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 164 239 (accept_3_2 64 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 164 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 164 239 (accept_3_2 61 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 164 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 164 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 164 239 (accept_3_2 58 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 164 239
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 56 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 164 239 (accept_3_2 55 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 164 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 164 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 164 239 (accept_3_2 52 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 164 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 164 239 (accept_3_2 49 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 164 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 164 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 239 (accept_3_2 46 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 164 239 (accept_3_2 43 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 164 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 164 239 (Polychromatic418967fa.accept_17_7_11_1_1_4503 41 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 239 (accept_3_2 40 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 239
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 38 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 164 239 (accept_3_2 37 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 164 239 (Polychromatic418967fa.accept_13_10_8_5_1_1616 36 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 164 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 239 (accept_3_2 34 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 239 (accept_3_2 31 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 239 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 239 (accept_3_2 28 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 239 (accept_3_2 25 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 239 (accept_3_2 22 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 239
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 239 (accept_3_2 19 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 239 (accept_3_2 16 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 239 (accept_3_2 13 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 239 (accept_3_2 10 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 239 (accept_3_2 7 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 239 (accept_3_2 4 164 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 239 (accept_3_2 1 164 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 163 239 (Eq.refl
  Bool.true) (allA_of_3_0 77 163 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 162 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 162 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 162 239 (accept_3_2 76 162 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 162 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 162 239
  (Polychromatic418967fa.accept_23_5_1_9_1_14297 74 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 162 239 (accept_3_2 73 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 162 239 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 162 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 162 239 (accept_3_2 70 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 162 239
  (Polychromatic418967fa.accept_13_3_6_5_1_2336 68 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 162 239 (accept_3_2 67 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 162 239 (Polychromatic418967fa.accept_13_1_6_5_1_1610 66 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 162 239 (accept_3_2 64 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 162 239 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 162 239
  (Polychromatic418967fa.accept_13_10_6_5_1_2297 62 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 162 239 (accept_3_2 61 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 162 239 (Polychromatic418967fa.accept_16_12_2_15_1_490 60 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 162 239 (Polychromatic418967fa.accept_17_8_9_1_1_3340 59 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 162 239 (accept_3_2 58 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 239
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 56 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 162 239 (accept_3_2 55 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 162 239 (Polychromatic418967fa.accept_15_9_12_14_1_963 54 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 239 (accept_3_2 52 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 162 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 51 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 239
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 50 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 162 239 (accept_3_2 49 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 162 239 (Polychromatic418967fa.accept_21_6_15_8_1_9895 48 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 162 239 (Polychromatic418967fa.accept_10_7_2_9_1_775 47 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 239 (accept_3_2 46 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 239
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 44 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 239 (accept_3_2 43 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 162 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 239 (accept_3_2 40 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 239 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 239
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 38 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 239 (accept_3_2 37 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 162 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 36 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 239 (Polychromatic418967fa.accept_14_7_8_1_1_1621 35 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 239 (accept_3_2 34 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 239
  (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 162 239 (accept_3_2 31 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 162 239 (Polychromatic418967fa.accept_13_4_6_5_1_2333 30 162 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 239 (accept_3_2 28 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 239 (Polychromatic418967fa.accept_10_7_2_9_1_775
  27 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 239
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 26 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 162 239 (accept_3_2 25 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 162 239 (Polychromatic418967fa.accept_13_11_6_5_1_2339 24 162 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 162
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 239 (accept_3_2 22 162
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 239
  (Polychromatic418967fa.accept_17_3_9_1_1_1344 20 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 239 (accept_3_2 19 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 162 239 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 239 (accept_3_2 16 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 239 (Polychromatic418967fa.accept_17_15_9_1_1_3363 15 162
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 239
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 14 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 239 (accept_3_2 13 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 162 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 162 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 11 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 239 (accept_3_2 10 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 239
  (Polychromatic418967fa.accept_17_8_9_1_1_3340 8 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 239 (accept_3_2 7 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  162 239 (Polychromatic418967fa.accept_21_6_15_8_1_9895 6 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 162 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 239 (accept_3_2 4 162 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 162 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 239
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 2 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 239 (accept_3_2 1 162 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 161 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 161 239 (Polychromatic418967fa.accept_17_9_8_1_1_7036
  77 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 239 (accept_3_2 76
  161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 239
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 161 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 161 239 (accept_3_2 73 161 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 161 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 161 239
  (Polychromatic418967fa.accept_19_14_9_11_1_7555 71 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 161 239 (accept_3_2 70 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 161 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 239 (Polychromatic418967fa.accept_10_8_1_9_1_413 68 161
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 161 239 (accept_3_2 67 161
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 161 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 161 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 239 (accept_3_2 64 161 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 161 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 239 (accept_3_2 61 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 239 (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 239 (accept_3_2 58 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 239 (accept_3_2 55 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 239 (Polychromatic418967fa.accept_16_5_1_15_1_3922 53 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 239 (accept_3_2 52 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 239 (accept_3_2 49 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 239 (accept_3_2 46 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 239
  (Polychromatic418967fa.accept_18_8_17_5_1_9273 44 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 239 (accept_3_2 43 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 239 (Polychromatic418967fa.accept_14_13_7_1_1_1618 41 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 239 (accept_3_2 40 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 239 (accept_3_2 37 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 239 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 239 (accept_3_2 34 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 239
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 32 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 239 (accept_3_2 31 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 239 (accept_3_2 28 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 239 (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 239 (accept_3_2 25 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 239 (Polychromatic418967fa.accept_21_2_14_8_1_6834 23 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 239 (accept_3_2 22 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 239 (accept_3_2 19 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 239 (Polychromatic418967fa.accept_19_17_9_11_1_6057 17 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 239 (accept_3_2 16 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 161 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 239 (accept_3_2 13 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 239 (accept_3_2 10 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 239 (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 239
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 239 (accept_3_2 7 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 239 (accept_3_2 4 161 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 161 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 239 (accept_3_2 1 161 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 160 239 (Eq.refl
  Bool.true) (allA_of_3_0 80 160 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 159 239 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 159 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 159 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 239 (accept_3_2 79 159 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 159 239 (Polychromatic418967fa.accept_18_6_15_5_1_6563 78 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 159 239
  (Polychromatic418967fa.accept_21_14_12_8_1_6833 77 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 159 239 (accept_3_2 76 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 159 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 159 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 159 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 239 (accept_3_2 73 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 239
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 159 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 159 239 (accept_3_2 70 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 159 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 159 239 (accept_3_2 67 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 159 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 159 239 (accept_3_2 64 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 239 (Polychromatic418967fa.accept_13_11_3_5_1_982 63 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 159 239 (accept_3_2 61 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 159 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 239 (accept_3_2 58 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 159 239 (accept_3_2 55 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 159 239 (Polychromatic418967fa.accept_13_2_3_5_1_2294 54 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 159 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 239 (accept_3_2 52 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 51 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 239 (accept_3_2 49 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 239 (accept_3_2 46 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 239 (accept_3_2 43 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 42 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 239 (accept_3_2 40 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 239 (accept_3_2 37 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 239 (accept_3_2 34 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 239 (accept_3_2 31 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 239 (accept_3_2 28 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 239 (accept_3_2 25 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 239 (Polychromatic418967fa.accept_15_8_9_14_1_4577 23 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 239 (accept_3_2 22 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 239 (accept_3_2 19 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 239 (accept_3_2 16 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 239 (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 239 (accept_3_2 13 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 239 (accept_3_2 10 159 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 239 (accept_3_2 7 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 239 (Polychromatic418967fa.accept_15_5_9_14_1_1724 5 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 239 (accept_3_2 4 159 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 239 (accept_3_2 1 159 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 158 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 158 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 80
  158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 158 239 (accept_3_2 79
  158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 158 239
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 78 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 158 239 (accept_3_2 76 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 158 239 (Polychromatic418967fa.accept_10_4_8_9_1_784
  74 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 158 239 (accept_3_2 73
  158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 158 239
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 72 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 158 239 (Polychromatic418967fa.accept_10_1_8_9_1_787 71 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 158 239 (accept_3_2 70 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 158 239 (Polychromatic418967fa.accept_7_5_4_1_1_412
  68 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 158 239 (accept_3_2 67
  158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 158 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 66 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 158 239 (accept_3_2 64 158 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 158 239 (Polychromatic418967fa.accept_11_7_4_8_1_1371
  62 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 158 239 (accept_3_2 61
  158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 158 239
  (Polychromatic418967fa.accept_21_18_11_8_1_5273 60 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 158 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 239 (accept_3_2 58 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 239
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 158 239 (accept_3_2 55 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 239 (accept_3_2 52 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 50 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 239 (accept_3_2 49 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 239 (Polychromatic418967fa.accept_13_9_2_5_1_2310 48 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 239 (accept_3_2 46 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 239
  (Polychromatic418967fa.accept_10_4_8_9_1_784 44 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 239 (accept_3_2 43 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 239 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 239 (accept_3_2 40 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 239 (accept_3_2 37 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 239 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 239 (Polychromatic418967fa.accept_13_9_2_5_1_2310 35 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 239 (accept_3_2 34 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 239 (accept_3_2 31 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 239 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 239 (accept_3_2 28 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 239 (accept_3_2 25 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 239 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 239 (accept_3_2 22 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 239 (accept_3_2 19 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 239 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 239 (accept_3_2 16 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 239
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 239 (accept_3_2 13 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 239 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 239 (accept_3_2 10 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 239 (accept_3_2 7 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 239 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 239 (accept_3_2 4 158 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 239
  (Polychromatic418967fa.accept_28_2_18_15_1_14296 2 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 158 239 (accept_3_2 1 158 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  158 239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 157 239
  (Eq.refl Bool.true) (allA_of_3_0 83 157 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 156 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 156 239 (accept_3_2 82 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 156 239 (Polychromatic418967fa.accept_18_9_12_5_1_864 81 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 156 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 80 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 156 239 (accept_3_2 79 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 156 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 156 239 (Polychromatic418967fa.accept_16_13_12_15_1_6290 77 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 156 239 (accept_3_2 76 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 156 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 75 156 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 156 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 156 239 (accept_3_2 73 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 156 239 (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 156 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 156 239 (accept_3_2 70 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 156 239
  (Polychromatic418967fa.accept_15_8_6_14_1_975 68 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 156 239 (accept_3_2 67 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 156 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 156 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 156 239 (accept_3_2 64 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 156 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 156 239 (accept_3_2 61 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 156 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 156 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 156 239 (accept_3_2 58 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 156 239 (Polychromatic418967fa.accept_17_6_3_1_1_7011 57 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 156 239 (accept_3_2 55 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 156 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 54 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 156 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 156 239 (accept_3_2 52 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 156 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 239
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 50 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 156 239 (accept_3_2 49 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 156 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 239 (accept_3_2 46 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 156 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 156 239 (accept_3_2 43 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 156 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 239 (accept_3_2 40 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 156 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 156 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 156 239 (accept_3_2 37 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 156 239 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 156 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 239 (accept_3_2 34 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 156 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 239
  (Polychromatic418967fa.accept_17_15_3_1_1_9696 32 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 156 239 (accept_3_2 31 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 156 239 (Polychromatic418967fa.accept_20_10_16_19_1_5674 30 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 156 239 (accept_3_2 28 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 156 239 (accept_3_2 25 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 156 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 156 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 239 (accept_3_2 22 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 239 (Polychromatic418967fa.accept_19_2_4_11_1_7507 21 156
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 239 (accept_3_2 19 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 156 239 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 156 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 239 (accept_3_2 16 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 156 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 239
  (Polychromatic418967fa.accept_22_14_2_19_1_12906 14 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 156 239 (accept_3_2 13 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 156 239 (Polychromatic418967fa.accept_19_12_4_11_1_6078 12 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 239 (Polychromatic418967fa.accept_8_3_4_7_1_475
  11 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 239 (accept_3_2 10
  156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 239
  (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 156 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 156 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 239 (accept_3_2 7 156 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 156 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 156 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235
  5 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 239 (accept_3_2 4
  156 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 156 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 156 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 239 (accept_3_2 1 156 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 155 239 (Eq.refl Bool.true) (allA_succ_of_accept 84 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 155 239
  (Polychromatic418967fa.accept_15_8_5_14_1_986 83 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 155 239 (accept_3_2 82 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 155 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 155 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 155 239 (accept_3_2 79 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 155 239
  (Polychromatic418967fa.accept_15_2_5_14_1_61 77 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 155 239 (accept_3_2 76 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 155 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 74 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 155 239 (accept_3_2 73 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 155 239 (Polychromatic418967fa.accept_13_7_12_5_1_1603 72 155
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 155 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 155 239 (accept_3_2 70 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 155 239 (accept_3_2 67 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 239
  (Polychromatic418967fa.accept_16_1_11_15_1_498 65 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 155 239 (accept_3_2 64 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 155 239 (Polychromatic418967fa.accept_24_15_11_23_1_14295 63 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 239 (accept_3_2 61 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 239
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 239 (accept_3_2 58 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 56 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 239 (accept_3_2 55 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 155
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 239 (accept_3_2 52 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 239 (Polychromatic418967fa.accept_17_16_2_1_1_4492 50 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 239 (accept_3_2 49 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 239
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 47 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 239 (accept_3_2 46 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 239 (accept_3_2 43 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 239
  (Polychromatic418967fa.accept_10_1_5_9_1_157 41 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 155 239 (accept_3_2 40 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 155 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 38 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 239 (accept_3_2 37 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 239 (accept_3_2 34 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 239 (accept_3_2 31 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 239
  (Polychromatic418967fa.accept_19_10_3_11_1_7587 29 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 239 (accept_3_2 28 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 239 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 155 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 239 (accept_3_2 25 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506
  24 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 239
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 239 (accept_3_2 22 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 239 (accept_3_2 19 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 239 (Polychromatic418967fa.accept_19_18_3_11_1_6066 18 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 239 (accept_3_2 16 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 14 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 239 (accept_3_2 13 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 239
  (Polychromatic418967fa.accept_10_1_5_9_1_157 11 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 239 (accept_3_2 10 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 239 (Polychromatic418967fa.accept_15_9_5_14_1_973 9 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 239 (accept_3_2 7 155 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 239
  (Polychromatic418967fa.accept_20_5_15_19_1_4225 5 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 239 (accept_3_2 4 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 155 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 239 (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 239 (accept_3_2 1 155 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 155
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 154 239
  (Eq.refl Bool.true) (allA_of_3_0 86 154 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 153 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 153 239 (accept_3_2 85 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 153 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 84 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 153 239
  (Polychromatic418967fa.accept_22_17_21_19_1_4790 83 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 153 239 (accept_3_2 82 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 153 239 (Polychromatic418967fa.accept_28_25_13_15_1_14294 81 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 80
  153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 153 239 (accept_3_2 79
  153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 153 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 77 153 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 239 (accept_3_2 76 153 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 153 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74
  153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 153 239 (accept_3_2 73
  153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 153 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 72 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 153 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 71 153 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 239 (accept_3_2 70 153 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 153 239 (Polychromatic418967fa.accept_13_4_10_5_1_1644 69 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 153 239 (accept_3_2 67 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 153 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 239 (accept_3_2 64 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 239 (accept_3_2 61 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 239 (Polychromatic418967fa.accept_13_8_10_5_1_977 60 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 239 (Polychromatic418967fa.accept_25_9_3_14_1_14293 59 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 239 (accept_3_2 58 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 239 (Polychromatic418967fa.accept_21_15_6_8_1_9888 57 153
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 239 (accept_3_2 55 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 239 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 239 (accept_3_2 52 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 153 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 239 (accept_3_2 49 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 239 (Polychromatic418967fa.accept_18_12_9_5_1_2771 48 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 239 (accept_3_2 46 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 153 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 239 (accept_3_2 43 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 239 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 239 (accept_3_2 40 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 39 153
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 239 (accept_3_2 37 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 36 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 239 (accept_3_2 34 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 153 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 239 (accept_3_2 31 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 239 (Polychromatic418967fa.accept_19_10_1_11_1_7532 29 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 239 (accept_3_2 28 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 153
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 239 (accept_3_2 25 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 24 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 239 (accept_3_2 22 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 239 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 239 (accept_3_2 19 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 239 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 239 (accept_3_2 16 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 153
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 239 (accept_3_2 13 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 239 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 239 (accept_3_2 10 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 153 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 239 (accept_3_2 7 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 239 (accept_3_2 4 153 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 153 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 239 (accept_3_2 1 153 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 152 239
  (Eq.refl Bool.true) (allA_succ_of_accept 87 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 152 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 152 239 (accept_3_2 85 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 152 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 152 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 152 239 (accept_3_2 82 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 152 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 152 239 (accept_3_2 79 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 152 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 152 239 (Polychromatic418967fa.accept_10_7_2_9_1_775 77 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 152 239 (accept_3_2 76 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 152 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 152 239 (accept_3_2 73 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 152 239 (Polychromatic418967fa.accept_15_12_2_14_1_5659 72 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 152 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 71 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 152 239 (accept_3_2 70 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 239
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 68 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 152 239 (accept_3_2 67 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 152 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 152 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 239 (accept_3_2 64 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 152 239 (accept_3_2 61 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 152 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 152 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 239 (accept_3_2 58 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 152 239 (accept_3_2 55 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 239 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 239 (accept_3_2 52 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 239 (accept_3_2 49 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 239 (accept_3_2 46 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 239
  (Polychromatic418967fa.accept_16_12_8_15_1_5119 44 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 152 239 (accept_3_2 43 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 152 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 152 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 152 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 239 (accept_3_2 40 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39
  152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 239 (accept_3_2 37 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 239 (Polychromatic418967fa.accept_16_4_8_15_1_1113 36 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 239 (Polychromatic418967fa.accept_15_5_2_14_1_1693 35 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 239 (accept_3_2 34 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 239 (accept_3_2 31 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 239 (accept_3_2 28 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 239 (accept_3_2 25 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 239 (Polychromatic418967fa.accept_16_7_8_15_1_6327 23 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 239 (accept_3_2 22 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 239 (accept_3_2 19 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 239 (accept_3_2 16 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 14 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 239 (accept_3_2 13 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 239 (accept_3_2 10 152 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 239
  (Polychromatic418967fa.accept_22_8_20_19_1_8153 8 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 239 (accept_3_2 7 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 239 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 239 (accept_3_2 4 152 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 239 (accept_3_2 1 152 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 151 239
  (Eq.refl Bool.true) (allA_of_3_0 89 151 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 150 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 150 239 (accept_3_2 88 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 150 239 (Polychromatic418967fa.accept_16_7_6_15_1_495 87 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 150 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 150 239 (accept_3_2 85 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 150 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 150 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 150 239 (accept_3_2 82 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 150 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 80 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 150 239 (accept_3_2 79 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 150 239 (Polychromatic418967fa.accept_17_10_14_1_1_5823 78 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 150 239 (accept_3_2 76 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 150 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 150 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 150 239 (accept_3_2 73 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 150 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 150 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 239 (accept_3_2 70 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 239 (accept_3_2 67 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 150 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 239 (accept_3_2 64 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 150 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 150 239 (accept_3_2 61 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 150 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 150 239 (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 239 (accept_3_2 58 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 150 239 (accept_3_2 55 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 150 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 239 (accept_3_2 52 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 239
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 50 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 239 (accept_3_2 49 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 150 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 150 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 239 (accept_3_2 46 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 239 (accept_3_2 43 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 150 239 (Polychromatic418967fa.accept_19_4_17_11_1_7527 42 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 239 (accept_3_2 40 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 239 (accept_3_2 37 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 150 239 (Polychromatic418967fa.accept_20_16_10_19_1_10100 36 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 150 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 239 (accept_3_2 34 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 239 (accept_3_2 31 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 150 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 239 (accept_3_2 28 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 239 (Polychromatic418967fa.accept_17_10_14_1_1_5823 27 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 239 (accept_3_2 25 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 150 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 239 (accept_3_2 22 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 239 (accept_3_2 19 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 239 (accept_3_2 16 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 239 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 239
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 14 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 150 239 (accept_3_2 13 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 150 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 150 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 239 (accept_3_2 10 150 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 239 (accept_3_2 7 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 239 (Polychromatic418967fa.accept_19_6_17_11_1_6039 6 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 239 (accept_3_2 4 150 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 150 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 239 (accept_3_2 1 150 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 149 239
  (Eq.refl Bool.true) (allA_succ_of_accept 90 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 239
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 89 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 239 (accept_3_2 88 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 239 (accept_3_2 85 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 239 (Polychromatic418967fa.accept_16_4_5_15_1_5083 84 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 239 (accept_3_2 82 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 81 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 239 (accept_3_2 79 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 239
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 77 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 239 (accept_3_2 76 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 75 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 239 (accept_3_2 73 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 239 (Polychromatic418967fa.accept_19_15_16_11_1_7689 72 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 239
  (Polychromatic418967fa.accept_19_14_16_11_1_9054 71 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 149 239 (accept_3_2 70 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 149 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 68 149
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 239 (accept_3_2 67 149
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 149 239 (Polychromatic418967fa.accept_16_1_5_15_1_2918 65 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 239 (accept_3_2 64 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 149 239 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 149 239 (accept_3_2 61 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 149 239 (Polychromatic418967fa.accept_22_16_17_19_1_14292 60 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 239 (accept_3_2 58 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 149 239 (Polychromatic418967fa.accept_21_15_2_8_1_14291 57 149
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 239
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 56 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 239 (accept_3_2 55 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 239 (Polychromatic418967fa.accept_13_1_6_5_1_1610 53 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 239 (accept_3_2 52 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 149
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 239 (accept_3_2 49 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 239 (accept_3_2 46 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 239
  (Polychromatic418967fa.accept_19_6_16_11_1_9041 44 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 149 239 (accept_3_2 43 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 239 (accept_3_2 40 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 239
  (Polychromatic418967fa.accept_24_15_5_23_1_9282 39 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 239 (accept_3_2 37 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 239
  (Polychromatic418967fa.accept_21_14_2_8_1_14281 35 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 149 239 (accept_3_2 34 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 149 239 (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 239 (Polychromatic418967fa.accept_19_13_16_11_1_6047 32
  149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 239 (accept_3_2 31
  149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 149 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 29 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 239 (accept_3_2 28 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 149 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 239 (accept_3_2 25
  149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 149 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 239 (accept_3_2 22 149 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 149 239 (Polychromatic418967fa.accept_19_2_16_11_1_6045 21 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 239 (accept_3_2 19 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 239 (accept_3_2 16 149 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 239 (Polychromatic418967fa.accept_19_15_16_11_1_7689 15 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 239 (accept_3_2 13 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 239 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 239 (accept_3_2 10 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 239 (Polychromatic418967fa.accept_25_9_24_14_1_14290 9 149
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 239
  (Polychromatic418967fa.accept_14_8_9_1_1_3313 8 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 239 (accept_3_2 7 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 239 (Polychromatic418967fa.accept_19_5_16_11_1_4727 5 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 239 (accept_3_2 4 149 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 149 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 239 (accept_3_2 1 149 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 148 239
  (Eq.refl Bool.true) (allA_of_3_0 92 148 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 147 239 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 239 (accept_3_2 91 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 239 (Polychromatic418967fa.accept_13_12_4_5_1_1637 90 147 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 239 (accept_3_2 88 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 239 (accept_3_2 85 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 83 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 239 (accept_3_2 82 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 239 (accept_3_2 79 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 239
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 77 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 239 (accept_3_2 76 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 239 (Polychromatic418967fa.accept_13_10_4_5_1_2331 75 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 239 (accept_3_2 73 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 239 (accept_3_2 70 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 239 (accept_3_2 67 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 239 (Polychromatic418967fa.accept_13_1_4_5_1_113 66 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 239 (accept_3_2 64 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 239 (Polychromatic418967fa.accept_19_6_14_11_1_7565 63 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 239 (accept_3_2 61 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 239
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 59 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 147 239 (accept_3_2 58 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 147 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 147 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 239 (accept_3_2 55 147 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 239 (Polychromatic418967fa.accept_13_2_4_5_1_3152
  54 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 239 (accept_3_2 52 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 239 (accept_3_2 49 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 239 (Polychromatic418967fa.accept_10_8_7_9_1_425 48 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 239 (accept_3_2 46 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 239 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 239 (accept_3_2 43 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 239
  (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 239 (accept_3_2 40 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 239 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 239 (accept_3_2 37 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 239 (accept_3_2 34 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 239 (accept_3_2 31 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 239 (Polychromatic418967fa.accept_20_10_7_19_1_4293 30 147 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 239 (accept_3_2 28 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 239 (Polychromatic418967fa.accept_13_1_4_5_1_113 27 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 239 (accept_3_2 25 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 239
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 239 (accept_3_2 22 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 239 (accept_3_2 19 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 239 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 239 (accept_3_2 16 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 239 (accept_3_2 13 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 239 (accept_3_2 10 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 239 (accept_3_2 7 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 239
  (Polychromatic418967fa.accept_19_5_14_11_1_6084 5 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 239 (accept_3_2 4 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 239 (Polychromatic418967fa.accept_19_3_14_11_1_2214 3 147 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 239 (accept_3_2 1 147 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 146
  239 (Eq.refl Bool.true) (allA_succ_of_accept 93 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 146 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 92 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 146 239 (accept_3_2 91 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 146 239 (Polychromatic418967fa.accept_20_10_6_19_1_5691 90 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 146 239 (accept_3_2 88 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 146 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 86 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 146 239 (accept_3_2 85 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 146 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 146 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 83 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 146 239 (accept_3_2 82 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 146 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 146 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 146 239 (accept_3_2 79 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 146 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 146 239 (accept_3_2 76 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 239
  (Polychromatic418967fa.accept_13_9_3_5_1_1605 74 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 146 239 (accept_3_2 73 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 146 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 146 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 146 239 (accept_3_2 70 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 239 (accept_3_2 67 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 239 (accept_3_2 64 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 239 (accept_3_2 61 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 239 (Polychromatic418967fa.accept_19_2_13_11_1_10497 59 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 239 (accept_3_2 58 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 239 (accept_3_2 55 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 239 (accept_3_2 52 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 239
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 239 (accept_3_2 49 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 239 (accept_3_2 46 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 239 (accept_3_2 43 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 239 (accept_3_2 40 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 239
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 239 (accept_3_2 37 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 239 (Polychromatic418967fa.accept_19_17_13_11_1_2222 36 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 146 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 239 (accept_3_2 34 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 239 (accept_3_2 31 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 239 (accept_3_2 28 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 239 (accept_3_2 25 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 239 (accept_3_2 22 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 20 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 239 (accept_3_2 19 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 18 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 239 (accept_3_2 16 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 239
  (Polychromatic418967fa.accept_13_1_3_5_1_140 14 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 239 (accept_3_2 13 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 239 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 239 (accept_3_2 10 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 239 (accept_3_2 7 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 239 (accept_3_2 4 146 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 239 (accept_3_2 1 146 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 145
  239 (Eq.refl Bool.true) (allA_of_3_0 95 145 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 144 239
  (Eq.refl Bool.true) (allA_succ_of_accept 95 144 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 95 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 144 239 (accept_3_2 94 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 144 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 93 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 144 239
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 92 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 144 239 (accept_3_2 91 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 144 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 90 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 144 239 (accept_3_2 88 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 144 239
  (Polychromatic418967fa.accept_13_8_1_5_1_3176 86 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 144 239 (accept_3_2 85 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 144 239 (Polychromatic418967fa.accept_13_6_1_5_1_3988 84 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 144 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 83 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 144 239 (accept_3_2 82 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 144 239 (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 144 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 80 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 144 239 (accept_3_2 79 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 144 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 78 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 144 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 77 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 239 (accept_3_2 76 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 239
  (Polychromatic418967fa.accept_13_9_1_5_1_964 74 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 144 239 (accept_3_2 73 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 144 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 72 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 144 239 (Polychromatic418967fa.accept_13_6_1_5_1_3988 71 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 239 (accept_3_2 70 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 144 239 (Polychromatic418967fa.accept_13_4_1_5_1_1628 69 144
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 144 239 (accept_3_2 67 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 144 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 65 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 239 (accept_3_2 64 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 144 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 63 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 239
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 62 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 144 239 (accept_3_2 61 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 144 239 (Polychromatic418967fa.accept_13_8_1_5_1_3176 60 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 239 (accept_3_2 58 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 239
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 56 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 144 239 (accept_3_2 55 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 53 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 239 (accept_3_2 52 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 239
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 239 (accept_3_2 49 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 48 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 239 (accept_3_2 46 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 239
  (Polychromatic418967fa.accept_27_17_9_23_1_14289 44 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 144 239 (accept_3_2 43 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 144 239 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 144 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 239 (Polychromatic418967fa.accept_17_7_8_1_1_1373 41 144
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 239 (accept_3_2 40 144
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 239
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 144 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 239 (accept_3_2 37 144 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 144 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 239
  (Polychromatic418967fa.accept_10_5_4_9_1_420 35 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 144 239 (accept_3_2 34 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 144 239 (Polychromatic418967fa.accept_13_6_1_5_1_3988 32 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 239 (accept_3_2 31 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 239 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 144
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 239
  (Polychromatic418967fa.accept_13_3_1_5_1_499 29 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 239 (accept_3_2 28 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 144 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 239 (accept_3_2 25 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 239
  (Polychromatic418967fa.accept_10_3_4_9_1_15 23 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 239 (accept_3_2 22 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 144 239 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 144 239 (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 239 (accept_3_2 19 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 144
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 239 (accept_3_2 16 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 144 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 239 (Polychromatic418967fa.accept_20_14_4_19_1_4288 14 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 239 (accept_3_2 13 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 144 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 239
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 239 (accept_3_2 10 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 239 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 239 (accept_3_2 7 144 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 239 (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 239 (accept_3_2 4 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 239 (Polychromatic418967fa.accept_20_2_4_19_1_5634 2 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 239 (accept_3_2 1 144 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 143
  239 (Eq.refl Bool.true) (allA_succ_of_accept 96 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 143 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 95 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 143 239 (accept_3_2 94 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 143 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 143 239 (accept_3_2 91 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 143 239 (Polychromatic418967fa.accept_20_10_3_19_1_2931 90 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 89 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 143 239 (accept_3_2 88 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 86 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 239 (accept_3_2 85 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 143 239 (accept_3_2 82 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 143 239 (Polychromatic418967fa.accept_15_5_8_14_1_432 80 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 239 (accept_3_2 79 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 143 239
  (Polychromatic418967fa.accept_19_1_10_11_1_4721 77 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 143 239 (accept_3_2 76 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 239 (accept_3_2 73 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 72
  143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 239
  (Polychromatic418967fa.accept_25_21_18_14_1_7190 71 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 143 239 (accept_3_2 70 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 239 (accept_3_2 67 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 66
  143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 239 (accept_3_2 64 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 239 (Polychromatic418967fa.accept_25_13_18_14_1_14288 63 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 239 (Polychromatic418967fa.accept_17_11_7_1_1_7023 62 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 239 (accept_3_2 61 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 60
  143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 239
  (Polychromatic418967fa.accept_17_8_7_1_1_4521 59 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 239 (accept_3_2 58 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 239 (accept_3_2 55 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 239
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 143 239 (accept_3_2 52 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 143 239 (Polychromatic418967fa.accept_15_5_8_14_1_432 50 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 239 (accept_3_2 49 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 239 (accept_3_2 46 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 239 (Polychromatic418967fa.accept_17_11_7_1_1_7023 45 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 239 (accept_3_2 43 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 239
  (Polychromatic418967fa.accept_19_3_10_11_1_7669 41 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 143 239 (accept_3_2 40 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 239 (accept_3_2 37 143 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207
  36 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 35 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 239 (accept_3_2 34 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 239 (accept_3_2 31 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 239 (accept_3_2 28 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 239 (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 239 (accept_3_2 25 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 239
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 239 (accept_3_2 22 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 239 (accept_3_2 19 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 239
  (Polychromatic418967fa.accept_27_17_8_23_1_14287 17 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 239 (accept_3_2 16 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 14 143
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 239 (accept_3_2 13 143
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 239
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 239 (accept_3_2 10 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 239 (Polychromatic418967fa.accept_17_8_7_1_1_4521
  8 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 239 (accept_3_2 7
  143 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 239
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 143 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 239 (accept_3_2 4 143 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 143 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 143 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 2
  143 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 239 (accept_3_2 1 143
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  142 239 (Eq.refl Bool.true) (allA_of_3_0 98 142 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 141 239
  (Eq.refl Bool.true) (allA_succ_of_accept 98 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 239 (accept_3_2 97 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 239 (Polychromatic418967fa.accept_18_6_15_5_1_6563 96 141
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 95 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 239 (accept_3_2 94 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 239 (accept_3_2 91 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 89 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 239 (accept_3_2 88 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 239 (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 239 (accept_3_2 85 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 83 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 239 (accept_3_2 82 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 239 (Polychromatic418967fa.accept_13_3_11_5_1_2348 81 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 239 (accept_3_2 79 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 239
  (Polychromatic418967fa.accept_19_1_8_11_1_3378 77 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 239 (accept_3_2 76 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 75 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 239 (accept_3_2 73 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 239 (accept_3_2 70 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 69 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 239 (accept_3_2 67 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 239 (accept_3_2 64 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 239 (accept_3_2 61 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 239 (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 141 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 239
  (Polychromatic418967fa.accept_13_7_11_5_1_2302 59 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 239 (accept_3_2 58 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 239 (accept_3_2 55 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 239 (accept_3_2 52 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 239 (accept_3_2 49 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 239 (accept_3_2 46 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 45 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 239 (accept_3_2 43 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 239
  (Polychromatic418967fa.accept_19_3_8_11_1_7609 41 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 239 (accept_3_2 40 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 239 (accept_3_2 37 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 239 (Polychromatic418967fa.accept_19_17_8_11_1_7605 36 141 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 239 (accept_3_2 34 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 239 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 239 (accept_3_2 31 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 239 (accept_3_2 28 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 239 (accept_3_2 25 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 141 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 239
  (Polychromatic418967fa.accept_15_8_6_14_1_975 23 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 239 (accept_3_2 22 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 239 (accept_3_2 19 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 239 (accept_3_2 16 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 239 (accept_3_2 13 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 239 (accept_3_2 10 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 9 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 239 (accept_3_2 7 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 239
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 239 (accept_3_2 4 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 141 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 239 (accept_3_2 1 141 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  140 239 (Eq.refl Bool.true) (allA_succ_of_accept 99 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 98 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 140 239 (accept_3_2 97 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 140 239 (Polychromatic418967fa.accept_15_6_5_14_1_429 96 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 140 239 (Polychromatic418967fa.accept_13_4_10_5_1_1644 95 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 140 239 (accept_3_2 94 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 140 239
  (Polychromatic418967fa.accept_15_2_5_14_1_61 92 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 140 239 (accept_3_2 91 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 140 239 (Polychromatic418967fa.accept_17_5_4_1_1_3369 90 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 140 239 (Polychromatic418967fa.accept_19_13_7_11_1_7551 89 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 140 239 (accept_3_2 88 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 86 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 140 239 (accept_3_2 85 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 140 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 84 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 140 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 140 239 (accept_3_2 82 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 140 239
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 80 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 140 239 (accept_3_2 79 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 140 239 (Polychromatic418967fa.accept_21_15_14_8_1_6826 78 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 140 239 (Polychromatic418967fa.accept_15_2_5_14_1_61 77 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 140 239 (accept_3_2 76 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 74 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 140 239 (accept_3_2 73 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 140 239 (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 140 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 71 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 140 239 (accept_3_2 70 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 239
  (Polychromatic418967fa.accept_15_8_5_14_1_986 68 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 140 239 (accept_3_2 67 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 239 (Polychromatic418967fa.accept_15_6_5_14_1_429 66 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 140 239 (Polychromatic418967fa.accept_17_14_4_1_1_3341 65 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 239 (accept_3_2 64 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 239 (accept_3_2 61 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 239 (Polychromatic418967fa.accept_13_8_10_5_1_977 60 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 239 (accept_3_2 58 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 239
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 56 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 140 239 (accept_3_2 55 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 140 239 (Polychromatic418967fa.accept_13_2_10_5_1_1643 54 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 140 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 53 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 239 (accept_3_2 52 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 140 239 (accept_3_2 49 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 140 239 (Polychromatic418967fa.accept_17_14_4_1_1_3341 48 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 140 239 (Polychromatic418967fa.accept_13_8_10_5_1_977 47 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 239 (accept_3_2 46 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 140 239
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 44 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 239 (accept_3_2 43 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 239 (Polychromatic418967fa.accept_17_8_4_1_1_5730 42 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 239 (Polychromatic418967fa.accept_13_2_10_5_1_1643 41 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 239 (accept_3_2 40 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 38 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 239 (accept_3_2 37 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 239 (Polychromatic418967fa.accept_15_6_5_14_1_429 36 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 239 (accept_3_2 34 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 239
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 32 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 239 (accept_3_2 31 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 239 (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 239 (Polychromatic418967fa.accept_16_13_12_15_1_6290 29 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 239 (accept_3_2 28 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 239 (accept_3_2 25 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 239 (Polychromatic418967fa.accept_15_9_5_14_1_973 24 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 239 (accept_3_2 22 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 239
  (Polychromatic418967fa.accept_16_4_12_15_1_6289 20 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 140 239 (accept_3_2 19 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 140 239 (Polychromatic418967fa.accept_16_2_12_15_1_2908 18 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 239
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 239 (accept_3_2 16 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 239 (accept_3_2 13 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 239 (Polychromatic418967fa.accept_19_12_7_11_1_7658 12 140
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 239 (accept_3_2 10 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 239 (Polychromatic418967fa.accept_13_8_10_5_1_977 8 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 239 (accept_3_2 7 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 239 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 140 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 239
  (Polychromatic418967fa.accept_17_5_4_1_1_3369 5 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 239 (accept_3_2 4 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 2 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 239 (accept_3_2 1 140 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 139 239 (Eq.refl Bool.true) (allA_of_3_0 101 139 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 138
  239 (Eq.refl Bool.true) (allA_succ_of_accept 101 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 138 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 138 239 (accept_3_2 100 138 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 138 239 (Polychromatic418967fa.accept_18_9_12_5_1_864
  99 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 138 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 98 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 138 239 (accept_3_2 97 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 138 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 96 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 138 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 138 239 (accept_3_2 94 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 138 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 92 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 138 239 (accept_3_2 91 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 138 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 138 239 (accept_3_2 88 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 138 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 138 239
  (Polychromatic418967fa.accept_15_11_3_14_1_971 86 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 138 239 (accept_3_2 85 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 138 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 84 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 138 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 239 (accept_3_2 82 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 138 239 (accept_3_2 79 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 138 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 78 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 239 (accept_3_2 76 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 239 (Polychromatic418967fa.accept_13_10_8_5_1_1616 75 138 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 239 (accept_3_2 73 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 138 239 (Polychromatic418967fa.accept_19_15_5_11_1_4719 72 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 138 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 239 (accept_3_2 70 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 239
  (Polychromatic418967fa.accept_13_3_8_5_1_974 68 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 138 239 (accept_3_2 67 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 138 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 239 (accept_3_2 64 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 239 (Polychromatic418967fa.accept_18_9_12_5_1_864 63 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 239 (accept_3_2 61 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 138 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 138 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 239 (accept_3_2 58 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 239 (accept_3_2 55 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 138 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 239 (accept_3_2 52 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 239
  (Polychromatic418967fa.accept_17_16_2_1_1_4492 50 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 239 (accept_3_2 49 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 239 (accept_3_2 46 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 239 (accept_3_2 43 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 239 (accept_3_2 40 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 239 (accept_3_2 37 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 239 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 239 (accept_3_2 34 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 239 (accept_3_2 31 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 239 (Polychromatic418967fa.accept_16_14_10_15_1_3969 30 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 239 (accept_3_2 28 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 239 (accept_3_2 25 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 239 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 239 (accept_3_2 22 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 239 (accept_3_2 19 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 239 (accept_3_2 16 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 239
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 239 (accept_3_2 13 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 239 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 239 (accept_3_2 10 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 239
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 239 (accept_3_2 7 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 239 (accept_3_2 4 138 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 239
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 239 (accept_3_2 1 138 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 137 239 (Eq.refl Bool.true) (allA_succ_of_accept 102 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 137
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 101 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 137 239 (accept_3_2 100 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 137 239 (Polychromatic418967fa.accept_26_21_7_5_1_14286 99 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 98 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 239 (accept_3_2 97 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 239
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 95 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 239 (accept_3_2 94 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 93 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 92 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 239 (accept_3_2 91 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 137 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 89 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 239 (accept_3_2 88 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 239 (accept_3_2 85 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 239
  (Polychromatic418967fa.accept_19_7_4_11_1_3414 83 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 239 (accept_3_2 82 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 239 (Polychromatic418967fa.accept_21_18_11_8_1_5273 81 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 239 (accept_3_2 79 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 239
  (Polychromatic418967fa.accept_13_12_7_5_1_3147 77 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 239 (accept_3_2 76 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 239 (accept_3_2 73 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 72 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 239 (accept_3_2 70 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 68 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 239 (accept_3_2 67 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 239
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 65 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 239 (accept_3_2 64 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 63 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 239 (accept_3_2 61 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 59 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 239 (accept_3_2 58 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 239 (Polychromatic418967fa.accept_16_8_9_15_1_5112 56 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 239 (accept_3_2 55 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 239 (accept_3_2 52 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 239 (accept_3_2 49 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 239
  (Polychromatic418967fa.accept_7_5_4_1_1_412 47 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 239 (accept_3_2 46 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 239 (accept_3_2 43 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 239
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 41 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 239 (accept_3_2 40 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 239 (accept_3_2 37 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 239 (accept_3_2 34 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 239 (Polychromatic418967fa.accept_10_2_7_9_1_783 32 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 239 (accept_3_2 31 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 239
  (Polychromatic418967fa.accept_24_5_17_23_1_14285 29 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 137 239 (accept_3_2 28 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 137 239 (Polychromatic418967fa.accept_15_12_2_14_1_5659 27 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 239 (accept_3_2 25
  137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 239
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 137 239 (Polychromatic418967fa.accept_25_23_12_14_1_14284 23 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 239 (accept_3_2 22 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 239
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 239 (accept_3_2 19 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 239 (accept_3_2 16 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 239 (accept_3_2 13 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 239 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 239 (accept_3_2 10 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 239 (Polychromatic418967fa.accept_25_9_12_14_1_10949 9 137
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 239 (accept_3_2 7 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 239 (accept_3_2 4 137 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 239 (accept_3_2 1 137 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 136 239 (Eq.refl Bool.true) (allA_of_3_0 104 136 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 135
  239 (Eq.refl Bool.true) (allA_succ_of_accept 104 135 239 (Polychromatic418967fa.accept_6_2_3_5_1_26 104 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 239 (accept_3_2 103 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 239
  (Polychromatic418967fa.accept_16_6_7_15_1_1942 102 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 101 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 135 239 (accept_3_2 100 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 135 239 (Polychromatic418967fa.accept_16_3_7_15_1_1130 99 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 135 239 (accept_3_2 97 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 135 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 96 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 135 239 (Polychromatic418967fa.accept_22_7_3_19_1_8158 95 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 135 239 (accept_3_2 94 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 135 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 93 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 135 239 (accept_3_2 91 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 135 239 (Polychromatic418967fa.accept_19_13_2_11_1_9083 89 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 135 239 (accept_3_2 88 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 87 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 135 239 (accept_3_2 85 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 135 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 84 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 239 (accept_3_2 82 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 135 239 (accept_3_2 79 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 135 239 (Polychromatic418967fa.accept_14_8_9_1_1_3313 78 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 135 239 (Polychromatic418967fa.accept_20_17_15_19_1_12975 77 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 239 (accept_3_2 76 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 239 (Polychromatic418967fa.accept_16_11_7_15_1_1998 75 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 239 (accept_3_2 73 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 135 239 (Polychromatic418967fa.accept_11_6_3_8_1_843 72 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 135 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 71 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 239 (accept_3_2 70 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 239 (accept_3_2 67 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 135 239 (Polychromatic418967fa.accept_19_8_2_11_1_7504 65 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 239 (accept_3_2 64 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 239 (Polychromatic418967fa.accept_17_12_16_1_1_8363 63 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 239 (accept_3_2 61 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 239 (accept_3_2 58 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 239 (accept_3_2 55 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 239 (Polychromatic418967fa.accept_10_4_5_9_1_1231 54 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 239 (Polychromatic418967fa.accept_17_2_16_1_1_2260 53 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 239 (accept_3_2 52 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 51 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 239 (accept_3_2 49 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 239 (Polychromatic418967fa.accept_19_9_2_11_1_7581 47 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 239 (accept_3_2 46 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 239 (accept_3_2 43 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 239 (Polychromatic418967fa.accept_19_4_2_11_1_3409 42 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 239 (accept_3_2 40 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 239 (Polychromatic418967fa.accept_11_6_3_8_1_843 39 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 239 (accept_3_2 37 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 239 (Polychromatic418967fa.accept_16_3_7_15_1_1130 35 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 239 (accept_3_2 34 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 239 (accept_3_2 31 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 239 (Polychromatic418967fa.accept_16_14_7_15_1_3947 30 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 239 (Polychromatic418967fa.accept_17_12_16_1_1_8363 29 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 239 (accept_3_2 28 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 239 (accept_3_2 25 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 239 (Polychromatic418967fa.accept_19_4_2_11_1_3409 23 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 239 (accept_3_2 22 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 21 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 239 (accept_3_2 19 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 239 (Polychromatic418967fa.accept_21_18_9_8_1_11479 18 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 239 (accept_3_2 16 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 239 (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 135 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 239 (accept_3_2 13 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 239 (Polychromatic418967fa.accept_17_12_16_1_1_8363 12 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 239 (accept_3_2 10 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 135
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 239 (accept_3_2 7 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 239 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 239 (accept_3_2 4 135 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 239 (accept_3_2 1 135 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 134 239 (Eq.refl Bool.true) (allA_succ_of_accept 105 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9
  105 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 134 239
  (Polychromatic418967fa.accept_11_5_2_8_1_866 104 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 134 239 (accept_3_2 103 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 102 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 101 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 134 239 (accept_3_2 100 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 134 239
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 98 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 134 239 (accept_3_2 97 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 96 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 134 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 95 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 134 239 (accept_3_2 94 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 134 239 (accept_3_2 91 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 134 239 (Polychromatic418967fa.accept_13_12_4_5_1_1637 90 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 134 239 (accept_3_2 88 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 134 239
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 86 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 134 239 (accept_3_2 85 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 134 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 134 239 (accept_3_2 82 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 134 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 80 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 134 239 (accept_3_2 79 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 134 239 (accept_3_2 76 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 134 239 (accept_3_2 73 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 134 239 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 134 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 239 (accept_3_2 70 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 239
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 68 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 239 (accept_3_2 67 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 239 (accept_3_2 64 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 239
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 62 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 239 (accept_3_2 61 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 239 (Polychromatic418967fa.accept_23_13_19_9_1_14283 59 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 239 (accept_3_2 58 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 239 (accept_3_2 55 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 239 (Polychromatic418967fa.accept_13_2_4_5_1_3152 54 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 239 (accept_3_2 52 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 239
  (Polychromatic418967fa.accept_17_16_15_1_1_11968 50 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 134 239 (accept_3_2 49 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 134 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 239 (accept_3_2 46 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45
  134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 239 (accept_3_2 43 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 239 (accept_3_2 40 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 239 (accept_3_2 37 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 239 (Polychromatic418967fa.accept_13_10_4_5_1_2331 36 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 239 (Polychromatic418967fa.accept_10_5_4_9_1_420 35 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 239 (accept_3_2 34 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 239
  (Polychromatic418967fa.accept_12_8_2_11_1_246 32 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 239 (accept_3_2 31 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 239 (accept_3_2 28 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 239
  (Polychromatic418967fa.accept_17_9_15_1_1_7048 26 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 239 (accept_3_2 25 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 239 (Polychromatic418967fa.accept_10_3_4_9_1_15 23 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 239 (accept_3_2 22 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 239 (accept_3_2 19 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 239 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 239 (accept_3_2 16 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 239
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 239 (accept_3_2 13 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 239 (accept_3_2 10 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 239
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 239 (accept_3_2 7 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 239 (accept_3_2 4 134 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 239 (accept_3_2 1 134 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 133 239 (Eq.refl Bool.true) (allA_of_3_0 107 133 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 132 239 (Eq.refl Bool.true) (allA_succ_of_accept 107 132 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 107 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 132 239 (accept_3_2 106 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 132 239 (Polychromatic418967fa.accept_14_7_6_1_1_1656 105 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 132 239 (Polychromatic418967fa.accept_16_8_4_15_1_2941 104 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 132 239 (accept_3_2 103 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 132
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 132 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 101 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 132 239 (accept_3_2 100 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 132 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 99 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 132 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 98 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 132 239 (accept_3_2 97 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 132 239
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 95 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 132 239 (accept_3_2 94 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 132 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 92 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 132 239 (accept_3_2 91 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 132 239 (Polychromatic418967fa.accept_13_12_2_5_1_1634 90 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 132 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 89 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 132 239 (accept_3_2 88 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 132 239 (Polychromatic418967fa.accept_10_7_2_9_1_775 87 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 86 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 239 (accept_3_2 85 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 83 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 132 239 (accept_3_2 82 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 132 239 (Polychromatic418967fa.accept_10_1_2_9_1_152 81 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 132 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 80 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 239 (accept_3_2 79 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 132 239 (Polychromatic418967fa.accept_16_14_4_15_1_3944 78 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 239
  (Polychromatic418967fa.accept_10_7_2_9_1_775 77 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 132 239 (accept_3_2 76 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 132 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 74 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 239 (accept_3_2 73 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 132 239 (accept_3_2 70 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 132 239 (Polychromatic418967fa.accept_13_4_2_5_1_4045 69 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 239 (accept_3_2 67 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 132 239 (accept_3_2 64 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 132 239 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 132 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 62 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 239 (accept_3_2 61 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 239 (Polychromatic418967fa.accept_16_12_4_15_1_5091 60 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 132 239 (accept_3_2 58 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 132 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 56 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 239 (accept_3_2 55 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 132 239 (accept_3_2 52 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 132 239 (Polychromatic418967fa.accept_19_12_18_11_1_9065 50 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 239 (accept_3_2 49 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 132 239 (accept_3_2 46 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 132 239 (Polychromatic418967fa.accept_19_7_18_11_1_464 45 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 239 (accept_3_2 43 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 239 (Polychromatic418967fa.accept_13_3_2_5_1_1632 42 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 239
  (Polychromatic418967fa.accept_10_1_2_9_1_152 41 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 132 239 (accept_3_2 40 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 132 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 239 (accept_3_2 37 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 239 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 239 (accept_3_2 34 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 132 239 (Polychromatic418967fa.accept_15_2_12_14_1_1709 32 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 239 (accept_3_2 31 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 239
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 132 239 (accept_3_2 28 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 132 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 239 (accept_3_2 25 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 239 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 132 239 (accept_3_2 22 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 132 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 132 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 239 (accept_3_2 19 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 239 (Polychromatic418967fa.accept_23_18_17_9_1_14282 18 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 239
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 239 (accept_3_2 16 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 132 239 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 132 239 (Polychromatic418967fa.accept_16_14_4_15_1_3944 14 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 239 (accept_3_2 13 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 132 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 239
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 239 (accept_3_2 10 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 132 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 239 (accept_3_2 7 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 239 (Polychromatic418967fa.accept_19_6_18_11_1_7636 6 132 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 239 (accept_3_2 4 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  132 239 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 132 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 239 (accept_3_2 1 132 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 131 239 (Eq.refl Bool.true) (allA_succ_of_accept 108 131 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 108 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 107 131 239 (Polychromatic418967fa.accept_13_3_1_5_1_499 107 131 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 239 (accept_3_2 106 131 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 105 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 105 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 104 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 131 239 (accept_3_2 103 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 102 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 101 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 239 (accept_3_2 100 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 239 (Polychromatic418967fa.accept_13_8_1_5_1_3176 99 131
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 131 239
  (Polychromatic418967fa.accept_10_8_1_9_1_413 98 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 131 239 (accept_3_2 97 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 131 239 (Polychromatic418967fa.accept_21_12_5_8_1_9929 96 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 95 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 239 (accept_3_2 94 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 93 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 131 239
  (Polychromatic418967fa.accept_8_4_3_7_1_491 92 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 131 239 (accept_3_2 91 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 90 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 131 239 (Polychromatic418967fa.accept_19_13_17_11_1_4716 89 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 131 239 (accept_3_2 88 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 87 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 239
  (Polychromatic418967fa.accept_11_9_10_8_1_444 86 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 239 (accept_3_2 85 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 239 (accept_3_2 82 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 81 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 239 (accept_3_2 79 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 239 (Polychromatic418967fa.accept_10_8_1_9_1_413 78 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 77 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 239 (accept_3_2 76 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 75 131
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 239 (accept_3_2 73 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 72 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 239 (Polychromatic418967fa.accept_13_6_1_5_1_3988 71 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 239 (accept_3_2 70 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 239
  (Polychromatic418967fa.accept_8_4_3_7_1_491 68 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 239 (accept_3_2 67 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 65 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 239 (accept_3_2 64 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 63 131
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 239 (accept_3_2 61 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 239 (accept_3_2 58 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 239 (Polychromatic418967fa.accept_15_12_11_14_1_3464 57 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 239
  (Polychromatic418967fa.accept_13_4_1_5_1_1628 56 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 239 (accept_3_2 55 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 239 (Polychromatic418967fa.accept_21_12_5_8_1_9929 54 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 239 (accept_3_2 52 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 239 (Polychromatic418967fa.accept_13_12_1_5_1_1650 51 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 239
  (Polychromatic418967fa.accept_16_2_3_15_1_6309 50 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 239 (accept_3_2 49 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 239 (Polychromatic418967fa.accept_13_8_1_5_1_3176 47 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 239 (accept_3_2 46 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 239
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 239 (accept_3_2 43 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 239 (Polychromatic418967fa.accept_10_2_1_9_1_1248 42 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 239 (accept_3_2 40 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 239
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 239 (accept_3_2 37 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 35 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 239 (accept_3_2 34 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 239 (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 131
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 239
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 239 (accept_3_2 31 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 239 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 239 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 239 (accept_3_2 28 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 239
  (Polychromatic418967fa.accept_23_3_16_9_1_7851 26 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 239 (accept_3_2 25 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 239 (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 239 (accept_3_2 22 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 239 (Polychromatic418967fa.accept_13_8_1_5_1_3176 21 131
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 239
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 239 (accept_3_2 19 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 239 (accept_3_2 16 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 239
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 14 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 239 (accept_3_2 13 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 239 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 239 (accept_3_2 10 131 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 239 (Polychromatic418967fa.accept_11_9_10_8_1_444
  9 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 239
  (Polychromatic418967fa.accept_10_8_1_9_1_413 8 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 239 (accept_3_2 7 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 239 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 239 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 239 (accept_3_2 4 131 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 239 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 239
  (Polychromatic418967fa.accept_10_2_1_9_1_1248 2 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 239 (accept_3_2 1 131 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 130 239 (Eq.refl Bool.true) (allA_of_3_0 110 130 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 129 239 (Eq.refl Bool.true) (allA_succ_of_accept 110 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 129 239 (accept_3_2 109 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 129 239 (Polychromatic418967fa.accept_13_4_12_5_1_476 108 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 107 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 129 239 (accept_3_2 106 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 129 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 105 129
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 129 239 (accept_3_2 103 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 129 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 101 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 129 239 (accept_3_2 100 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 129 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 99 129
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 129 239 (accept_3_2 97 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 96 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 95 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 129 239 (accept_3_2 94 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 93 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 129 239 (accept_3_2 91 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 89 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 239 (accept_3_2 88 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 239 (accept_3_2 85 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 84 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 129 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 83 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 239 (accept_3_2 82 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 239 (accept_3_2 79 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 239 (Polychromatic418967fa.accept_17_9_10_1_1_3345 77 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 239 (accept_3_2 76 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 129 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 239 (accept_3_2 73 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 239 (accept_3_2 70 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 239 (accept_3_2 67 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 239 (accept_3_2 64 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 239 (accept_3_2 61 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 239 (Polychromatic418967fa.accept_13_7_12_5_1_1603 59 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 239 (accept_3_2 58 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 239 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 129
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 239 (accept_3_2 55 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 239 (accept_3_2 52 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 239 (accept_3_2 49 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 239 (Polychromatic418967fa.accept_17_14_10_1_1_4523 48 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 239 (accept_3_2 46 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 239 (Polychromatic418967fa.accept_13_6_12_5_1_2304 45 129 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 239 (accept_3_2 43 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 239 (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 239 (accept_3_2 40 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 129 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 239 (accept_3_2 37 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 239 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 239 (accept_3_2 34 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 239 (accept_3_2 31 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 239 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 239 (accept_3_2 28 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 239 (accept_3_2 25 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 239 (accept_3_2 22 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 239 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 129 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 239 (accept_3_2 19 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 239 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 239 (accept_3_2 16 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 239 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 239 (accept_3_2 13 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 239 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 239 (accept_3_2 10 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 239 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 239 (accept_3_2 7 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 239 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 239 (accept_3_2 4 129 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 239 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 129 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 239 (accept_3_2 1 129 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 128 239 (Eq.refl Bool.true) (allA_succ_of_accept 111 128 239
  (Polychromatic418967fa.accept_6_3_2_5_1_32 111 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 128 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 110 128 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 128 239 (accept_3_2 109 128 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 108 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 107 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 128 239 (accept_3_2 106 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 105 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 104 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 128 239 (accept_3_2 103 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 128 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 102 128
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 128 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 101 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 128 239 (accept_3_2 100 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 99 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 128 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 98 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 128 239 (accept_3_2 97 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 128 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 96 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 128 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 95 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 128 239 (accept_3_2 94 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 128 239 (Polychromatic418967fa.accept_11_4_7_8_1_1926 92 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 128 239 (accept_3_2 91 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 90 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 89 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 128 239 (accept_3_2 88 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 128 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 86 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 128 239 (accept_3_2 85 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 128 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 128 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 83 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 128 239 (accept_3_2 82 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 80 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 128 239 (accept_3_2 79 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 128 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 128 239
  (Polychromatic418967fa.accept_10_7_8_9_1_785 77 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 128 239 (accept_3_2 76 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 128 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 74 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 128 239 (accept_3_2 73 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 128 239 (Polychromatic418967fa.accept_13_7_11_5_1_2302 72 128
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 128 239 (accept_3_2 70 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 128 239 (Polychromatic418967fa.accept_13_3_11_5_1_2348 68 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 128 239 (accept_3_2 67 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 128 239
  (Polychromatic418967fa.accept_15_5_8_14_1_432 65 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 128 239 (accept_3_2 64 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 62 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 128 239 (accept_3_2 61 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 128 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 128 239
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 128 239 (accept_3_2 58 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 128 239 (Polychromatic418967fa.accept_21_14_2_8_1_14281 56 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 128 239 (accept_3_2 55 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 128 239 (Polychromatic418967fa.accept_10_4_8_9_1_784 54 128
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 128 239 (accept_3_2 52 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 128 239 (Polychromatic418967fa.accept_12_2_8_11_1_31 50 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 239 (accept_3_2 49 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 239
  (Polychromatic418967fa.accept_10_7_8_9_1_785 47 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 239 (accept_3_2 46 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 239 (accept_3_2 43 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 239 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 239
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 239 (accept_3_2 40 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 239 (accept_3_2 37 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 239 (Polychromatic418967fa.accept_14_8_2_1_1_1652 36 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 239 (accept_3_2 34 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 239 (Polychromatic418967fa.accept_13_6_11_5_1_133 32 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 239 (accept_3_2 31 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 239
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 239 (accept_3_2 28 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 239 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 239 (accept_3_2 25 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 239
  (Polychromatic418967fa.accept_22_1_18_19_1_3294 23 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 128 239 (accept_3_2 22 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 239 (accept_3_2 19 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 239
  (Polychromatic418967fa.accept_24_18_8_23_1_14280 18 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 239 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 239 (accept_3_2 16 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 239
  (Polychromatic418967fa.accept_10_4_8_9_1_784 14 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 239 (accept_3_2 13 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 239 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 239 (Polychromatic418967fa.accept_10_1_8_9_1_787 11 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 239 (accept_3_2 10 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 239
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 239 (accept_3_2 7 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 239 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 239 (Polychromatic418967fa.accept_15_5_8_14_1_432 5 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 239 (accept_3_2 4 128 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 239 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 239
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 239 (accept_3_2 1 128 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 127 239 (Eq.refl Bool.true) (allA_of_3_0 113 127 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 126 239 (Eq.refl Bool.true) (allA_succ_of_accept 113 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9
  113 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 126 239 (accept_3_2
  112 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 126 239
  (Polychromatic418967fa.accept_22_1_16_19_1_6445 111 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 126 239 (Polychromatic418967fa.accept_15_5_6_14_1_1721 110 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 126 239 (accept_3_2 109 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 126 239 (Polychromatic418967fa.accept_13_4_9_5_1_1641 108 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 126 239
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 107 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 126 239 (accept_3_2 106 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 105 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 126 239 (Polychromatic418967fa.accept_23_12_11_9_1_14279 104 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 126 239 (accept_3_2 103 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 126 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 102 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 126 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 101 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 126 239 (accept_3_2 100 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 126 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 99 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 126 239 (Polychromatic418967fa.accept_15_8_6_14_1_975 98 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 126 239 (accept_3_2 97 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 126 239 (Polychromatic418967fa.accept_17_11_7_1_1_7023 96 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 126 239
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 95 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 126 239 (accept_3_2 94 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 126 239 (Polychromatic418967fa.accept_13_1_9_5_1_1598 92 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 126 239 (accept_3_2 91 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 126 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 89 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 126 239 (accept_3_2 88 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 126 239 (Polychromatic418967fa.accept_16_7_14_15_1_2932 87 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 126 239 (Polychromatic418967fa.accept_19_10_12_11_1_7622 86 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 239 (accept_3_2 85 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 126 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 84 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 126 239
  (Polychromatic418967fa.accept_10_3_6_9_1_779 83 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 126 239 (accept_3_2 82 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 126 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 80 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 239 (accept_3_2 79 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 239 (Polychromatic418967fa.accept_17_10_7_1_1_7024 78 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 126 239
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 126 239 (accept_3_2 76 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 126 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 75 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 126 239 (Polychromatic418967fa.accept_16_10_14_15_1_2933 74 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 239 (accept_3_2 73 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 239 (Polychromatic418967fa.accept_25_22_1_14_1_14278 72
  126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 239
  (Polychromatic418967fa.accept_16_7_14_15_1_2932 71 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 126 239 (accept_3_2 70 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 68 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 239 (accept_3_2 67 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 239
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 66 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 239 (accept_3_2 64 126 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 126 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 63 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 239
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 62 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 239 (accept_3_2 61 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 126 239 (Polychromatic418967fa.accept_19_3_12_11_1_7619 60 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 126 239 (Polychromatic418967fa.accept_17_8_7_1_1_4521 59 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 239 (accept_3_2 58 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 239
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 56 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 126 239 (accept_3_2 55 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 126 239 (Polychromatic418967fa.accept_13_2_9_5_1_959 54 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 239 (accept_3_2 52 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 239 (Polychromatic418967fa.accept_19_13_12_11_1_1249 51 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 239
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 50 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 239 (accept_3_2 49 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 126 239 (Polychromatic418967fa.accept_19_10_12_11_1_7622 48 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 47 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 239 (accept_3_2 46 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 239
  (Polychromatic418967fa.accept_17_10_7_1_1_7024 44 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 239 (accept_3_2 43 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 126 239 (Polychromatic418967fa.accept_13_3_9_5_1_2340 42 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 239 (accept_3_2 40 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 239 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 239
  (Polychromatic418967fa.accept_15_8_6_14_1_975 38 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 126 239 (accept_3_2 37 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 126 239 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 126 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 35 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 239 (accept_3_2 34 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 239
  (Polychromatic418967fa.accept_19_13_12_11_1_1249 32 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 126 239 (accept_3_2 31 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 126 239 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 126 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 239 (accept_3_2 28 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 239 (Polychromatic418967fa.accept_13_1_9_5_1_1598
  27 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 239
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 26 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 126 239 (accept_3_2 25 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 126 239 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 126 239 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 23 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 239 (accept_3_2 22 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 239
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 239 (accept_3_2 19 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 239 (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 239 (accept_3_2 16 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 239 (Polychromatic418967fa.accept_10_5_6_9_1_2235 15 126
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 239
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 239 (accept_3_2 13 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 239 (Polychromatic418967fa.accept_22_12_16_19_1_12914 12 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 239 (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 239 (accept_3_2 10 126 239
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 239
  (Polychromatic418967fa.accept_15_8_6_14_1_975 8 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 239 (accept_3_2 7 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 239 (Polychromatic418967fa.accept_27_6_18_23_1_14277 6 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 239 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 239 (accept_3_2 4 126 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 239 (Polychromatic418967fa.accept_10_3_6_9_1_779 3 126 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 239
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 239 (accept_3_2 1 126 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  239))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 125 239 (Eq.refl Bool.true) (allA_succ_of_accept 114 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 114 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 125 239 (Polychromatic418967fa.accept_15_8_5_14_1_986 113 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 239 (accept_3_2 112 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 111 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 110 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 239 (accept_3_2 109 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 239 (Polychromatic418967fa.accept_16_12_13_15_1_1966 108 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 107 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 239 (accept_3_2 106 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 105 125
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 239
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 104 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 125 239 (accept_3_2 103 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 102 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 125 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 101 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 239 (accept_3_2 100 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 239 (Polychromatic418967fa.accept_15_9_5_14_1_973 99 125
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 98 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 239 (accept_3_2 97 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 96 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 125 239 (Polychromatic418967fa.accept_11_7_4_8_1_1371 95 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 125 239 (accept_3_2 94 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 93 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 92 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 125 239 (accept_3_2 91 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 89 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 239 (accept_3_2 88 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 87 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 239 (accept_3_2 85 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 83 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 239 (accept_3_2 82 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 81 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 239
  (Polychromatic418967fa.accept_17_12_6_1_1_4517 80 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 125 239 (accept_3_2 79 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 125 239 (Polychromatic418967fa.accept_13_12_8_5_1_976 77 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 239 (accept_3_2 76 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 75 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 239 (accept_3_2 73 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 71 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 239 (accept_3_2 70 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 239
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 239 (accept_3_2 67 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 239 (accept_3_2 64 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 63 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 239 (accept_3_2 61 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 239 (Polychromatic418967fa.accept_21_17_20_8_1_9938 59 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 239 (accept_3_2 58 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 239 (accept_3_2 55 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 239 (Polychromatic418967fa.accept_13_1_8_5_1_2315 53 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 239 (accept_3_2 52 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 239 (accept_3_2 49 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 239 (accept_3_2 46 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 239 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 239
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 239 (accept_3_2 43 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 239 (Polychromatic418967fa.accept_10_1_5_9_1_157 41 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 239 (accept_3_2 40 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 239 (accept_3_2 37 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 239 (Polychromatic418967fa.accept_10_6_5_9_1_1233 36 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 239 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 239 (accept_3_2 34 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 239
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 239 (accept_3_2 31 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 239 (accept_3_2 28 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 239 (Polychromatic418967fa.accept_13_1_8_5_1_2315 27 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 239 (accept_3_2 25 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 239 (accept_3_2 22 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 239
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 239 (accept_3_2 19 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 239 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 239 (accept_3_2 16 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 239 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 125 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 239 (accept_3_2 13 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 239 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 239 (accept_3_2 10 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 239 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 239
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 239 (accept_3_2 7 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 239 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 239 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 239 (accept_3_2 4 125 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 239 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 125 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 239
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 239 (accept_3_2 1 125 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 124 239 (Eq.refl Bool.true) (allA_of_3_0 116 124 239 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 123 239 (Eq.refl Bool.true) (allA_succ_of_accept 116 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 116 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 123 239 (accept_3_2 115 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 123 239 (Polychromatic418967fa.accept_10_4_3_9_1_1262 114 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 123 239 (Polychromatic418967fa.accept_16_1_11_15_1_498 113 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 123 239 (accept_3_2 112 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 111 123
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 110 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 123 239 (accept_3_2 109 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 108 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 123 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 107 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 123 239 (accept_3_2 106 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 123 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 105
  123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 104 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 123 239 (accept_3_2 103 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 102 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 101 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 123 239 (accept_3_2 100 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 123 239 (Polychromatic418967fa.accept_16_3_11_15_1_1963 99 123
  239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 98 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 123 239 (accept_3_2 97 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 96 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 123 239 (Polychromatic418967fa.accept_13_4_6_5_1_2333 95 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 123 239 (accept_3_2 94 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 93 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 92 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 123 239 (accept_3_2 91 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 123 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 90 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 89 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 123 239 (accept_3_2 88 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 87 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 86 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 123 239 (accept_3_2 85 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 123 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 123 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 123 239 (accept_3_2 82 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 123 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 81 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 123 239 (accept_3_2 79 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 123 239 (Polychromatic418967fa.accept_18_6_15_5_1_6563 78 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 123 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 77 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 123 239 (accept_3_2 76 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 75 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 74 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 123 239 (accept_3_2 73 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 123 239 (Polychromatic418967fa.accept_19_15_9_11_1_7514 72 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 123 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 239 (accept_3_2 70 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 123 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 239 (accept_3_2 67 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 123 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 239 (accept_3_2 64 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 123 239 (Polychromatic418967fa.accept_13_11_6_5_1_2339 63 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 239 (accept_3_2 61 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 123 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 239 (accept_3_2 58 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 239 (accept_3_2 55 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 123 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 239 (accept_3_2 52 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 123 239 (Polychromatic418967fa.accept_13_12_6_5_1_2335 51 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 123 239 (accept_3_2 49 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 239 (accept_3_2 46 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 239 (accept_3_2 43 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 123 239 (Polychromatic418967fa.accept_13_3_6_5_1_2336 42 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 123 239 (Polychromatic418967fa.accept_15_11_3_14_1_971 41 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 239 (accept_3_2 40 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 239 (accept_3_2 37 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 123 239 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 123 239 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 239 (accept_3_2 34 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 123 239 (accept_3_2 31 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 123 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 239 (accept_3_2 28 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 123 239 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 239 (accept_3_2 25 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 123 239 (Polychromatic418967fa.accept_13_10_6_5_1_2297 23 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 239 (accept_3_2 22 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 123 239 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 239 (accept_3_2 19 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 123 239 (Polychromatic418967fa.accept_14_4_11_1_1_940 18 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 239 (accept_3_2 16 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 239 (Polychromatic418967fa.accept_19_15_9_11_1_7514 15 123 239
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 123 239 (accept_3_2 13 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 123 239 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 239 (accept_3_2 10 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 123 239 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 239 (accept_3_2 7 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  123 239 (Polychromatic418967fa.accept_10_6_3_9_1_1207 6 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 123 239 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 239 (accept_3_2 4 123 239 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 123 239 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 123 239 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 123 239
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 239 (accept_3_2 1 123 239 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  239)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_239_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


