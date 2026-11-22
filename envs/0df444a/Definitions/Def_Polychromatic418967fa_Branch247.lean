-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch247
-- name    : Polychromatic418967fa_Branch247
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:44.166146+00:00
-- url     : https://prove2.me/theorems/82f2a66f-b7ec-4a60-ba6c-8bf28f779fa6
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch247_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_247 : allB 247 247 :=
  allB_succ' 2 246 247 (Eq.refl Bool.true) (allA_succ_of_accept 1 246 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  246 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 247)) (allB_succ' 3 245 247
  (Eq.refl Bool.true) (allA_of_3_1 3 245 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 244 247 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 244 247 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 244 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 247 (accept_3_3 2 244 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 244 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 244 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 247)))) (allB_succ' 5 243 247 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 243 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 243 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 243 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 247 (accept_3_3 2 243 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 247
  (Polychromatic418967fa.accept_26_1_9_13_1_14994 1 243 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 243 247))))) (allB_succ' 6 242 247 (Eq.refl Bool.true) (allA_of_3_1 6 242 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 7 241 247 (Eq.refl Bool.true) (allA_succ_of_accept 6 241 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 241 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 247 (accept_3_3 5 241 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 247 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 241 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 241 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 247 (accept_3_3 2 241 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 241 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 247))))))) (allB_succ' 8 240 247 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 240 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 240 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 247 (Polychromatic418967fa.accept_21_6_9_16_1_2939 6 240
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 240 247 (accept_3_3 5 240 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 240 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092
  4 240 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 240 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 240 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 240 247 (accept_3_3 2 240 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  240 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 240 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 240 247)))))))) (allB_succ' 9 239 247 (Eq.refl Bool.true) (allA_of_3_1 9 239 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 238 247 (Eq.refl Bool.true) (allA_succ_of_accept 9 238 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 238 247 (accept_3_3 8 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  238 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 238 247 (Polychromatic418967fa.accept_15_6_13_7_1_222 6 238 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 247 (accept_3_3 5 238 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 238 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 238 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 238 247 (accept_3_3 2 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  238 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 238 247)))))))))) (allB_succ' 11 237 247 (Eq.refl Bool.true) (allA_succ_of_accept 10 237 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 237 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 237 247 (Polychromatic418967fa.accept_16_9_13_7_1_1509 9 237 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 247 (accept_3_3 8 237 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 237 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 237 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  237 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 237 247 (accept_3_3 5 237
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 247 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 237 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 237 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 237 247 (accept_3_3 2 237 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  237 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 237 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 237 247))))))))))) (allB_succ' 12 236 247 (Eq.refl Bool.true) (allA_of_3_1 12 236 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 235 247 (Eq.refl Bool.true) (allA_succ_of_accept 12 235 247
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 247 (accept_3_3 11 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 247 (Polychromatic418967fa.accept_11_10_4_5_1_359 10 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 247 (Polychromatic418967fa.accept_21_9_4_16_1_9022 9 235 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 247 (accept_3_3 8 235 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 235 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 247
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 247 (accept_3_3 5 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 235 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 235 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 247 (accept_3_3 2 235 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 235 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 247))))))))))))) (allB_succ' 14 234 247 (Eq.refl
  Bool.true) (allA_succ_of_gcd 13 234 247 13 1 18 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 234 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 234 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 247 (accept_3_3 11 234 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 247 (Polychromatic418967fa.accept_17_10_13_9_1_3913 10 234
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 234 247 (accept_3_3 8 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  234 247 (Polychromatic418967fa.accept_21_7_3_16_1_7337 7 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 234 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 234 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 247 (accept_3_3 5 234 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 247 (Polychromatic418967fa.accept_17_4_13_9_1_921 4 234 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 247
  (Polychromatic418967fa.accept_10_3_4_7_1_353 3 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 234 247 (accept_3_3 2 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  234 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 234 247)))))))))))))) (allB_succ' 15 233 247 (Eq.refl Bool.true) (allA_of_3_1 15 233 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 232 247 (Eq.refl Bool.true) (allA_succ_of_accept 15 232 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 232 247 (accept_3_3 14 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 232 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 232 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 232 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 232 247 (accept_3_3 11 232 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 232 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 232 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 232 247 (accept_3_3 8 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  232 247 (Polychromatic418967fa.accept_21_7_1_16_1_9032 7 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 232 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 232 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 247 (accept_3_3 5 232 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 247 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 232 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 232 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 232 247 (accept_3_3 2 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  232 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 232 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 232 247)))))))))))))))) (allB_succ' 17 231 247 (Eq.refl Bool.true) (allA_succ_of_accept 16 231
  247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 231 247 (Polychromatic418967fa.accept_22_15_11_5_1_13490 15 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 247 (accept_3_3 14 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 231 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 231 247
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 231 247 (accept_3_3 11 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 231 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 231 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 9 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 247 (accept_3_3 8 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 231 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 231 247
  (Polychromatic418967fa.accept_10_6_1_7_1_342 6 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 231 247 (accept_3_3 5 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  231 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 231 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 231 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 247 (accept_3_3 2 231 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 231 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 247))))))))))))))))) (allB_succ' 18 230 247 (Eq.refl
  Bool.true) (allA_of_3_1 18 230 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 229 247 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 229 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 247 (accept_3_3 17 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 229 247 (Polychromatic418967fa.accept_17_16_8_9_1_1772 16 229 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 247
  (Polychromatic418967fa.accept_22_15_9_5_1_14988 15 229 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 229 247 (accept_3_3 14 229 247 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 229 247 (Polychromatic418967fa.accept_21_13_19_16_1_721 13 229 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 247 (Polychromatic418967fa.accept_10_2_9_7_1_720
  12 229 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 247 (accept_3_3 11
  229 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 229 247 (Polychromatic418967fa.accept_25_9_4_22_1_13219 9 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 247 (accept_3_3 8 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 229 247 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 229 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  229 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 247 (accept_3_3 5 229
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 247
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 229 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 229 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 247 (accept_3_3 2 229 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 229 247 (Polychromatic418967fa.accept_17_1_8_9_1_1810 1 229 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 247))))))))))))))))))) (allB_succ' 20 228 247 (Eq.refl
  Bool.true) (allA_succ_of_gcd 19 228 247 19 1 12 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 18 228 247 (Polychromatic418967fa.accept_24_18_12_7_1_14861 18 228 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 247 (accept_3_3 17 228 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 247 (Polychromatic418967fa.accept_9_7_3_4_1_218
  16 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 247
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 228 247 (accept_3_3 14 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 228 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 228 247 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 228 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 247 (accept_3_3 11 228 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 228 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 247
  (Polychromatic418967fa.accept_10_9_8_7_1_714 9 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 228 247 (accept_3_3 8 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  228 247 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 228 247 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 228 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 247 (accept_3_3 5 228 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 247 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 228 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 247
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 228 247 (accept_3_3 2 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  228 247 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 228 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 228 247)))))))))))))))))))) (allB_succ' 21 227 247 (Eq.refl Bool.true) (allA_of_3_1 21 227 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 226 247 (Eq.refl Bool.true) (allA_succ_of_accept 21 226 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 226 247 (accept_3_3 20 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 226 247 (Polychromatic418967fa.accept_18_1_10_13_1_500 19 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 226 247 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 226 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 226 247 (accept_3_3 17 226 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 226 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 226 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 226 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 226 247 (accept_3_3 14 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 226 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 226 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 226 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 226 247 (accept_3_3 11 226 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 226 247 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 226 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 226 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 226 247 (accept_3_3 8 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  226 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 226 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 226 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 226 247 (accept_3_3 5 226 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 226 247 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 226 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 226 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 226 247 (accept_3_3 2 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  226 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 226 247)))))))))))))))))))))) (allB_succ' 23 225 247 (Eq.refl Bool.true) (allA_succ_of_accept 22
  225 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 225 247 (Polychromatic418967fa.accept_18_3_9_13_1_1235 21 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 247 (accept_3_3 20 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 247 (Polychromatic418967fa.accept_17_2_4_9_1_2791 19 225
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 225 247 (accept_3_3 17 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 225 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 225 247 (Polychromatic418967fa.accept_12_3_9_7_1_472 15 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 247 (accept_3_3 14 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 247 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 225 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 247
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 247 (accept_3_3 11 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 225 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 225 247 (Polychromatic418967fa.accept_20_9_5_7_1_6336 9 225 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 247 (accept_3_3 8 225 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 247 (Polychromatic418967fa.accept_27_7_9_4_1_14993 7 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 225 247 (accept_3_3 5 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  225 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 225 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 225 247 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 225 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 247 (accept_3_3 2 225 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 247 (Polychromatic418967fa.accept_21_1_15_16_1_5891 1 225 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 247))))))))))))))))))))))) (allB_succ' 24 224 247
  (Eq.refl Bool.true) (allA_of_3_1 24 224 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 223 247 (Eq.refl
  Bool.true) (allA_succ_of_accept 24 223 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 247 (accept_3_3 23 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 223 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 247
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 247 (accept_3_3 20 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 247 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 247 (accept_3_3 17 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 247 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 223 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 247
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 247 (accept_3_3 14 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 247 (Polychromatic418967fa.accept_27_13_7_4_1_14992 13 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 247 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 247 (accept_3_3 11 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 223 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 247
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 247 (accept_3_3 8 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 247 (Polychromatic418967fa.accept_17_7_2_9_1_6396 7 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 247 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 247 (accept_3_3 5 223 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 223 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 247 (accept_3_3 2 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 223 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 247))))))))))))))))))))))))) (allB_succ' 26 222 247 (Eq.refl Bool.true) (allA_succ_of_accept
  25 222 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 222 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 222 247 (accept_3_3 23 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 247 (Polychromatic418967fa.accept_26_22_14_13_1_14991 22 222 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 222 247 (accept_3_3 20 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 222 247 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 222 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 222 247 (accept_3_3 17 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 222 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 247
  (Polychromatic418967fa.accept_10_5_2_7_1_345 15 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 222 247 (accept_3_3 14 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 222 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 222 247 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 222 247 (accept_3_3 11 222 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 247 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 222 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 247
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 222 247 (accept_3_3 8 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  222 247 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 222 247 (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 222 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 222 247 (accept_3_3 5 222 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 247 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 222 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 247
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 222 247 (accept_3_3 2 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  222 247 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 222 247)))))))))))))))))))))))))) (allB_succ' 27 221 247 (Eq.refl Bool.true) (allA_of_3_1 27 221
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 220 247 (Eq.refl Bool.true) (allA_succ_of_accept 27 220
  247 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 220 247 (accept_3_3 26 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 220 247 (Polychromatic418967fa.accept_17_8_16_9_1_8952 25 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 220 247 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 220 247 (accept_3_3 23 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 220 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 220 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 220 247 (accept_3_3 20 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 220 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 220 247 (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 247 (accept_3_3 17 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 220 247 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 220
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 220 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 220 247 (accept_3_3 14 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 247 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 220 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 247 (accept_3_3 11 220 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 220 247 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 247 (accept_3_3 8 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 247 (Polychromatic418967fa.accept_18_7_4_13_1_3315 7 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 247 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 220 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 247 (accept_3_3 5 220 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 247 (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 220 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 247
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 247 (accept_3_3 2 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 247 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 220 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 247)))))))))))))))))))))))))))) (allB_succ' 29 219 247 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 219 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 247 (Polychromatic418967fa.accept_18_9_3_13_1_5905 27 219
  247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 247 (accept_3_3 26 219
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 219 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 219 247 (accept_3_3 23 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 219 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 219 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 247 (Polychromatic418967fa.accept_12_9_3_7_1_924
  21 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 247 (accept_3_3 20
  219 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 219 247 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 219 247 (accept_3_3 17 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 219 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 219 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 247 (Polychromatic418967fa.accept_9_6_3_4_1_477
  15 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 247 (accept_3_3 14
  219 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 247
  (Polychromatic418967fa.accept_15_13_9_7_1_2194 13 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 219 247 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 219 247 (accept_3_3 11 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 219 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 219 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 247 (Polychromatic418967fa.accept_12_9_3_7_1_924 9
  219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 247 (accept_3_3 8 219
  247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 247
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 219 247 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 219 247 (accept_3_3 5 219 247 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 219 247 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 247 (Polychromatic418967fa.accept_16_3_11_7_1_770
  3 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 247 (accept_3_3 2
  219 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 247
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 219 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 219 247))))))))))))))))))))))))))))) (allB_succ' 30 218 247 (Eq.refl Bool.true) (allA_of_3_1 30 218 247
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 217 247 (Eq.refl Bool.true) (allA_succ_of_accept 30 217 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 247 (accept_3_3 29 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 247 (Polychromatic418967fa.accept_18_10_1_13_1_2192 28 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 247 (Polychromatic418967fa.accept_17_10_13_9_1_3913 27 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 247 (accept_3_3 26 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 217 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 247
  (Polychromatic418967fa.accept_9_6_1_4_1_474 24 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 247 (accept_3_3 23 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 247 (accept_3_3 20 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 247 (Polychromatic418967fa.accept_14_5_7_9_1_3828 19 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 247 (accept_3_3 17 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 247 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 247 (accept_3_3 14 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 247 (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 247
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 247 (accept_3_3 11 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 247 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 247 (Polychromatic418967fa.accept_20_9_17_7_1_4748 9 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 247 (accept_3_3 8 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 247 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 217 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 247
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 247 (accept_3_3 5 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 247 (Polychromatic418967fa.accept_17_4_13_9_1_921 4 217 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 247 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 247 (accept_3_3 2 217 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 247 (Polychromatic418967fa.accept_21_1_7_16_1_5859 1 217 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 247))))))))))))))))))))))))))))))) (allB_succ' 32
  216 247 (Eq.refl Bool.true) (allA_succ_of_accept 31 216 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 216 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 216 247
  (Polychromatic418967fa.accept_21_9_6_16_1_5857 30 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 216 247 (accept_3_3 29 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 216 247 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 216 247 (Polychromatic418967fa.accept_15_12_6_7_1_1353 27 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 247 (accept_3_3 26 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 216 247
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 247
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 216 247 (accept_3_3 23 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 216 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 216 247 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 216 247 (accept_3_3 20 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 247 (Polychromatic418967fa.accept_25_19_16_22_1_14990 19
  216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 247
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 216 247 (accept_3_3 17 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 216 247 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 216 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 216 247 (accept_3_3 14 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 247 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 247
  (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 216 247 (accept_3_3 11 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 216 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 216 247 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 216 247 (accept_3_3 8 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 247 (Polychromatic418967fa.accept_21_7_6_16_1_5834 7 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 247
  (Polychromatic418967fa.accept_20_6_16_7_1_9232 6 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 216 247 (accept_3_3 5 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  216 247 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 216 247 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 216 247 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 247 (accept_3_3 2 216 247 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 247 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 216 247 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 247))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_247_segment_001)))))))))))))))))))))))))))))))


