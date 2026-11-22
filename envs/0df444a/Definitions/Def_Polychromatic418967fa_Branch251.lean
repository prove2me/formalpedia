-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch251
-- name    : Polychromatic418967fa_Branch251
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:26.240933+00:00
-- url     : https://prove2.me/theorems/005f5f82-8f5b-4169-a9c2-16696c2193cd
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch251_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_251 : allB 251 251 :=
  allB_succ' 2 250 251 (Eq.refl Bool.true) (allA_of_3_0 2 250 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  249 251 (Eq.refl Bool.true) (allA_succ_of_accept 2 249 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 249 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 251 (accept_3_2 1 249 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 251))) (allB_succ' 4 248 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 248 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 248 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 248 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 248 251 (accept_3_2 1 248 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248 251)))) (allB_succ' 5 247 251 (Eq.refl Bool.true) (allA_of_3_0
  5 247 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 246 251 (Eq.refl Bool.true) (allA_succ_of_accept 5
  246 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 246 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 246 251 (accept_3_2 4 246 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 246 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 246 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 246 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 246 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 251 (accept_3_2 1 246 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 251)))))) (allB_succ' 7 245 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 245 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 245 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 245 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 251 (accept_3_2 4 245 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  245 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 245 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 251 (accept_3_2 1 245 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245 251)))))))
  (allB_succ' 8 244 251 (Eq.refl Bool.true) (allA_of_3_0 8 244 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 243 251 (Eq.refl Bool.true) (allA_succ_of_accept 8 243 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 251 (accept_3_2 7 243 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 251 (Polychromatic418967fa.accept_13_6_9_4_1_2288
  6 243 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 243 251
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 243 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 243 251 (accept_3_2 4 243 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  243 251 (Polychromatic418967fa.accept_21_3_12_20_1_1891 3 243 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 243 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 243 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 251 (accept_3_2 1 243 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 243 251))))))))) (allB_succ' 10 242 251 (Eq.refl Bool.true) (allA_succ_of_accept 9 242
  251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 242 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 242 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 242 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 251 (accept_3_2 7 242 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 242 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 242 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  242 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 251 (accept_3_2 4 242
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 251 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 242 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 242 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 251 (accept_3_2 1 242 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  251)))))))))) (allB_succ' 11 241 251 (Eq.refl Bool.true) (allA_of_3_0 11 241 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 240 251 (Eq.refl Bool.true) (allA_succ_of_accept 11 240 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 240 251 (accept_3_2 10 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  240 251 (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 240 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 240 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 251 (accept_3_2 7 240 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 251 (Polychromatic418967fa.accept_17_6_2_13_1_3051 6 240 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 240 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 240 251 (accept_3_2 4 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  240 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 240 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 240 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 240 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 251 (accept_3_2 1 240 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 240 251)))))))))))) (allB_succ' 13 239 251 (Eq.refl Bool.true) (allA_succ_of_accept 12
  239 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 239 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 251 (accept_3_2 10 239 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 239 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 251
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 251 (accept_3_2 7 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 239 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 251 (accept_3_2 4 239 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 239 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 251
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 251 (accept_3_2 1 239 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  251))))))))))))) (allB_succ' 14 238 251 (Eq.refl Bool.true) (allA_of_3_0 14 238 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 237 251 (Eq.refl Bool.true) (allA_succ_of_accept 14 237 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 251 (accept_3_2 13 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 237 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 251 (accept_3_2 10 237 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 251 (Polychromatic418967fa.accept_17_9_16_13_1_6636 9 237 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 251 (accept_3_2 7 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 237 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 251 (accept_3_2 4 237 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 237 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 251 (accept_3_2 1 237 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  251))))))))))))))) (allB_succ' 16 236 251 (Eq.refl Bool.true) (allA_succ_of_accept 15 236 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 236 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 236 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 251 (accept_3_2 13 236 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 236 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 236 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 251 (Polychromatic418967fa.accept_7_4_5_6_1_344
  11 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 236 251 (accept_3_2 10
  236 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 236 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 236 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 236 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 251 (accept_3_2 7 236 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 236 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 236 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5
  236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 251 (accept_3_2 4 236
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 251 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 251
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 236 251 (accept_3_2 1 236 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  251)))))))))))))))) (allB_succ' 17 235 251 (Eq.refl Bool.true) (allA_of_3_0 17 235 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 234 251 (Eq.refl Bool.true) (allA_succ_of_accept 17 234 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 234 251 (accept_3_2 16 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 234 251 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 234 251 (Polychromatic418967fa.accept_25_14_9_1_1_15174 14 234 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 251 (accept_3_2 13 234 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 234 251 (Polychromatic418967fa.accept_16_12_10_11_1_2667 12
  234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 234 251 (accept_3_2 10 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  234 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 234 251 (Polychromatic418967fa.accept_24_8_18_11_1_10133 8 234 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 251 (accept_3_2 7 234 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 234 251 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 234 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 234 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 251 (accept_3_2 4 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  234 251 (Polychromatic418967fa.accept_14_3_10_13_1_339 3 234 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 234 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 234 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 251 (accept_3_2 1 234 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 234 251)))))))))))))))))) (allB_succ' 19 233 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 233 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 233 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 233 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 251 (accept_3_2 16 233 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 251 (accept_3_2 13 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 251 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 233 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 251 (accept_3_2 10 233 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 251 (Polychromatic418967fa.accept_19_9_5_4_1_1866 9 233 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 251 (accept_3_2 7 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 251 (Polychromatic418967fa.accept_13_5_12_4_1_449 5 233 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 251 (accept_3_2 4 233 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 233 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 251 (accept_3_2 1 233 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  251))))))))))))))))))) (allB_succ' 20 232 251 (Eq.refl Bool.true) (allA_of_3_0 20 232 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 231 251 (Eq.refl Bool.true) (allA_succ_of_accept 20 231 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 251 (accept_3_2 19 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 251 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 231 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 251 (accept_3_2 16 231 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 251 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 231
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 251 (accept_3_2 13 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 251 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 231 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 251 (accept_3_2 10 231 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 231 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 251 (accept_3_2 7 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 251 (Polychromatic418967fa.accept_13_6_10_4_1_957 6 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 231 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 251 (accept_3_2 4 231 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 231 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 251 (accept_3_2 1 231 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  251))))))))))))))))))))) (allB_succ' 22 230 251 (Eq.refl Bool.true) (allA_succ_of_accept 21 230 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 230 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 230 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 251 (accept_3_2 19 230 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 230 251 (Polychromatic418967fa.accept_13_5_9_4_1_441 18 230 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 230 251 (accept_3_2 16 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 230 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 230 251 (Polychromatic418967fa.accept_19_14_2_4_1_8473 14 230 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 251 (accept_3_2 13 230 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 230 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 230 251 (accept_3_2 10 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  230 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 230 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 230 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 251 (accept_3_2 7 230 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 230 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 230 251 (accept_3_2 4 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  230 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 230 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 230 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 230 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 251 (accept_3_2 1 230 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 251)))))))))))))))))))))) (allB_succ' 23 229 251 (Eq.refl Bool.true) (allA_of_3_0
  23 229 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 228 251 (Eq.refl Bool.true) (allA_succ_of_accept 23
  228 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 228 251 (accept_3_2 22 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 228 251 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 228 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 228 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 228 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 251 (accept_3_2 19 228 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 228 251
  (Polychromatic418967fa.accept_20_18_8_11_1_9699 18 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 228 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 251 (accept_3_2 16 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 228 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 228 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 228 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 251 (accept_3_2 13 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 228 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 228 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 251 (accept_3_2 10 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 228 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 228 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 228 251
  (Polychromatic418967fa.accept_15_8_3_11_1_849 8 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 228 251 (accept_3_2 7 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  228 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 228 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 251 (accept_3_2 4 228 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 228 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 228 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 228 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 251 (accept_3_2 1 228 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228
  251)))))))))))))))))))))))) (allB_succ' 25 227 251 (Eq.refl Bool.true) (allA_succ_of_accept 24 227 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 24 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 227 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 227 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 251 (accept_3_2 22 227 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 227 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 251 (Polychromatic418967fa.accept_13_7_6_4_1_933
  20 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 251 (accept_3_2 19
  227 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 227 251 (Polychromatic418967fa.accept_19_17_18_4_1_12571 17 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 251 (accept_3_2 16 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 227 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 251 (accept_3_2 13 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 251 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 251 (accept_3_2 10 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 227 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 251
  (Polychromatic418967fa.accept_16_8_3_11_1_4763 8 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 251 (accept_3_2 7 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 251 (accept_3_2 4 227 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 227 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 251 (accept_3_2 1 227 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  251))))))))))))))))))))))))) (allB_succ' 26 226 251 (Eq.refl Bool.true) (allA_of_3_0 26 226 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 225 251 (Eq.refl Bool.true) (allA_succ_of_accept 26 225 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 225 251 (accept_3_2 25 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 225 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 225 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 225 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 251 (accept_3_2 22 225 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 225 251 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 225 251 (accept_3_2 19 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 225 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 225 251 (Polychromatic418967fa.accept_20_17_5_11_1_9622 17 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 251 (accept_3_2 16 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 225 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 225
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 251 (accept_3_2 13 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 225 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 225 251 (Polychromatic418967fa.accept_19_11_16_4_1_7075 11 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 251 (accept_3_2 10 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 225 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 225 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 251 (accept_3_2 7 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  225 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 225 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 225 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 251 (accept_3_2 4 225 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 225 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 225 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 251 (accept_3_2 1 225 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225
  251))))))))))))))))))))))))))) (allB_succ' 28 224 251 (Eq.refl Bool.true) (allA_succ_of_accept 27 224 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 224 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 224 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 251 (accept_3_2 25 224 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 224 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 224 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 224 251
  (Polychromatic418967fa.accept_18_5_8_17_1_3478 23 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 224 251 (accept_3_2 22 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 224 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 224 251 (Polychromatic418967fa.accept_13_7_3_4_1_459 20 224 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 251 (accept_3_2 19 224 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 251 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 224
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 224 251
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 224 251 (accept_3_2 16 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 224 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 224 251 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 224 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 251 (accept_3_2 13 224 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 251 (Polychromatic418967fa.accept_13_12_3_4_1_928 12 224
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 224 251
  (Polychromatic418967fa.accept_19_11_15_4_1_7010 11 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 224 251 (accept_3_2 10 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 224 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 251 (Polychromatic418967fa.accept_17_8_3_13_1_5372 8 224
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 251 (accept_3_2 7 224 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 224 251 (Polychromatic418967fa.accept_19_6_15_4_1_1851
  6 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 251
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 224 251 (accept_3_2 4 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  224 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 224 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 224 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 251 (accept_3_2 1 224 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 251)))))))))))))))))))))))))))) (allB_succ' 29 223 251 (Eq.refl Bool.true)
  (allA_of_3_0 29 223 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 222 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 222 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 222 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 251 (accept_3_2 28 222 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 222 251 (Polychromatic418967fa.accept_19_8_13_4_1_15140 27 222 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 251
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 222 251 (accept_3_2 25 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 222 251 (Polychromatic418967fa.accept_21_3_12_20_1_1891 24 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 222 251 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 251 (accept_3_2 22 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 222 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 251 (accept_3_2 19 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 222 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 251 (accept_3_2 16 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 222 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 222 251 (accept_3_2 13 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 222 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 222 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 251 (accept_3_2 10 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 222 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 222 251 (accept_3_2 7 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  222 251 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 222 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 251 (accept_3_2 4 222 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 222 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 251 (accept_3_2 1 222 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  251)))))))))))))))))))))))))))))) (allB_succ' 31 221 251 (Eq.refl Bool.true) (allA_succ_of_accept 30 221 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 221 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 221 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 251 (accept_3_2 28 221 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 221 251 (Polychromatic418967fa.accept_19_8_12_4_1_2981 27 221 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 251 (accept_3_2 25 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 251 (accept_3_2 22 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 251 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 221 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 251
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 251 (accept_3_2 19 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 251 (accept_3_2 16 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 251 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 221 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 251 (accept_3_2 13 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 251 (accept_3_2 10 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 221 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 251
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 8 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 251 (accept_3_2 7 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 251 (accept_3_2 4 221 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 221 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 251 (accept_3_2 1 221 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  251))))))))))))))))))))))))))))))) (allB_succ' 32 220 251 (Eq.refl Bool.true) (allA_of_3_0 32 220 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 219 251 (Eq.refl Bool.true) (allA_succ_of_accept 32 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 251 (accept_3_2 31 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 219 251 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 251 (accept_3_2 28 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 251 (Polychromatic418967fa.accept_19_8_10_4_1_4292 27 219 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 251 (accept_3_2 25 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 251 (accept_3_2 22 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 219 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 251 (accept_3_2 19 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 251 (accept_3_2 16 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 219 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 251 (accept_3_2 13 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 251 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 251 (accept_3_2 10 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 219 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 251 (accept_3_2 7 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 251 (accept_3_2 4 219 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 251
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 251 (accept_3_2 1 219 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  251))))))))))))))))))))))))))))))))) (allB_succ' 34 218 251 (Eq.refl Bool.true) (allA_succ_of_accept 33 218 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 218 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 218 251 (accept_3_2 31 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 218 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 218 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 251 (accept_3_2 28
  218 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 251
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 218 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 218 251 (accept_3_2 25 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 218 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 218 251 (Polychromatic418967fa.accept_7_2_1_6_1_173
  23 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 251 (accept_3_2 22
  218 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 218 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 251 (accept_3_2 19 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 218 251 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 218 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 251 (accept_3_2 16 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 251 (accept_3_2 13 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 251 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 218 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 251
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 218 251 (accept_3_2 10 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 218 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 218 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 251 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 218 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 251 (accept_3_2 7 218 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 6
  218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 251
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 251 (accept_3_2 4 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 218 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 251 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 251 (accept_3_2 1 218 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 218 251)))))))))))))))))))))))))))))))))) (allB_succ' 35 217 251 (Eq.refl Bool.true)
  (allA_of_3_0 35 217 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 216 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 216 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 216 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 251 (accept_3_2 34 216 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 216 251 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 216 251
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 251 (accept_3_2 31 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 216 251 (Polychromatic418967fa.accept_19_11_7_4_1_4308 30 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 216 251 (Polychromatic418967fa.accept_16_13_8_11_1_4785 29 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 251 (accept_3_2 28 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 216 251 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 216
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 216 251
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 216 251 (accept_3_2 25 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 216 251 (Polychromatic418967fa.accept_11_2_7_9_1_890 24 216 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 216 251 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 216
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 251 (accept_3_2 22 216
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 216 251
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 21 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 216 251 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 216 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 251 (accept_3_2 19 216 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 216 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 216 251
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 251 (accept_3_2 16 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 216 251 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 216 251 (Polychromatic418967fa.accept_19_14_7_4_1_4210 14 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 251 (accept_3_2 13 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 216
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 251
  (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 251 (accept_3_2 10 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  216 251 (Polychromatic418967fa.accept_13_9_8_4_1_937 9 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 216 251 (Polychromatic418967fa.accept_22_8_18_9_1_5631 8 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 251 (accept_3_2 7 216 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 251 (Polychromatic418967fa.accept_20_6_16_11_1_2379 6 216
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 251
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 251 (accept_3_2 4 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 251 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 216 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 251 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 216 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 251 (accept_3_2 1 216 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 216 251)))))))))))))))))))))))))))))))))))) (allB_succ' 37 215 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 215 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 215 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 251 (Polychromatic418967fa.accept_13_9_7_4_1_953 35 215
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 251 (accept_3_2 34 215
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 215 251
  (Polychromatic418967fa.accept_20_13_15_11_1_6610 33 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 251 (accept_3_2 31 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 251 (Polychromatic418967fa.accept_20_10_15_11_1_3759 30 215 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 251
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 251 (accept_3_2 28 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 251 (Polychromatic418967fa.accept_21_6_5_20_1_12265 27 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 251 (accept_3_2 25 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 215
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 251
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 251 (accept_3_2 22 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 251 (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 20 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 251 (accept_3_2 19 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 251 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 251
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 251 (accept_3_2 16 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 251 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 251 (accept_3_2 13 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 215 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 251
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 251 (accept_3_2 10 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 251 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 251 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 251 (accept_3_2 7 215 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 251 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 251
  (Polychromatic418967fa.accept_16_5_7_11_1_2664 5 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 251 (accept_3_2 4 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 251 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 215 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 251 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 251 (accept_3_2 1 215 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 215 251))))))))))))))))))))))))))))))))))))) (allB_succ' 38 214 251 (Eq.refl
  Bool.true) (allA_of_3_0 38 214 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 213 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 213 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 251 (accept_3_2 37 213 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 213 251 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 213 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 251
  (Polychromatic418967fa.accept_11_2_4_9_1_484 35 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 251 (accept_3_2 34 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 251 (Polychromatic418967fa.accept_17_16_9_13_1_3087 33 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 251 (accept_3_2 31 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 213 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 251
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 251 (accept_3_2 28 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 251 (accept_3_2 25 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 251 (Polychromatic418967fa.accept_11_2_4_9_1_484 24 213 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 251
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 251 (accept_3_2 22 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 251 (accept_3_2 19 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 213 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 251
  (Polychromatic418967fa.accept_21_17_3_20_1_6054 17 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 213 251 (accept_3_2 16 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 213 251 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 213 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 213 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 251 (accept_3_2 13 213 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 251 (Polychromatic418967fa.accept_9_3_6_8_1_308
  12 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 251
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 251 (accept_3_2 10 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 251 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 251 (accept_3_2 7 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 213 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 251
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 251 (accept_3_2 4 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 251 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 213 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 251 (accept_3_2 1 213 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 251))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 212 251 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 38
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 212 251 (accept_3_2 37
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 212 251
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 212 251 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 251 (accept_3_2 34 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 251 (Polychromatic418967fa.accept_7_4_2_6_1_337
  32 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 212 251 (accept_3_2 31
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 212 251
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 212 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 251 (accept_3_2 28 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 251 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 251 (accept_3_2 25
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 212 251
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 212 251 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 251 (accept_3_2 22 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 251 (accept_3_2 19
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 212 251
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 212 251 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 251 (accept_3_2 16 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 251 (Polychromatic418967fa.accept_12_2_8_11_1_31
  14 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 251 (accept_3_2 13
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 251
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 212 251 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 251 (accept_3_2 10 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 251 (Polychromatic418967fa.accept_7_1_2_6_1_55 8
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 251 (accept_3_2 7 212
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 251
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 212 251 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 251 (accept_3_2 4 212 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 212 251 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 251 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  212 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 251 (accept_3_2 1 212
  251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212 251)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41
  211 251 (Eq.refl Bool.true) (allA_of_3_0 41 211 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 210 251
  (Eq.refl Bool.true) (allA_succ_of_accept 41 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 210 251 (accept_3_2 40 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 210 251 (Polychromatic418967fa.accept_16_7_2_11_1_931 39 210
  251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 210 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 210 251 (accept_3_2 37 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 210 251 (Polychromatic418967fa.accept_17_2_6_13_1_2056 36 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 210 251 (Polychromatic418967fa.accept_19_16_1_4_1_4235 35 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 210 251 (accept_3_2 34 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 210 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 210 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 210 251 (accept_3_2 31 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 210 251 (Polychromatic418967fa.accept_24_6_18_11_1_6604 30 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 251 (accept_3_2 28 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 210 251 (Polychromatic418967fa.accept_18_9_12_17_1_6060 27 210 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 210 251
  (Polychromatic418967fa.accept_19_7_1_4_1_12606 26 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 251 (accept_3_2 25 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 210 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 210 251 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 251 (accept_3_2 22 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 210 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 210 251 (accept_3_2 19 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 210 251 (Polychromatic418967fa.accept_13_5_2_4_1_3955 18 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 251 (accept_3_2 16 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 210 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 210 251
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 251 (accept_3_2 13 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 210 251 (Polychromatic418967fa.accept_13_12_2_4_1_3131 12 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 210 251 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 251 (accept_3_2 10 210 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 251
  (Polychromatic418967fa.accept_24_8_18_11_1_10133 8 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 210 251 (accept_3_2 7 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 210 251 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 210 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 251 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 210 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 251 (accept_3_2 4 210 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 251 (Polychromatic418967fa.accept_19_3_1_4_1_1860
  3 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 251
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 210 251 (accept_3_2 1 210 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210
  251)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 209 251 (Eq.refl Bool.true) (allA_succ_of_accept 42 209
  251 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 209 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 251 (accept_3_2 40 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 209 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 251 (accept_3_2 37
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 251
  (Polychromatic418967fa.accept_13_10_1_4_1_3103 36 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 209 251 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 251 (accept_3_2 34 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 209 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 251 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 251 (accept_3_2 31
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 209 251 (Polychromatic418967fa.accept_13_3_1_4_1_945 29 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 251 (accept_3_2 28 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 209 251 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 209 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 251
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 251 (accept_3_2 25 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 251 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 251 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 251 (accept_3_2 22 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 209 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 251
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 209 251 (accept_3_2 19 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 209 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 251 (Polychromatic418967fa.accept_22_17_11_9_1_10636 17
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 251 (accept_3_2 16
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 251
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 209 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 251 (accept_3_2 13 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 209 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 251
  (Polychromatic418967fa.accept_23_11_2_21_1_3600 11 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 209 251 (accept_3_2 10 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 209 251 (Polychromatic418967fa.accept_17_9_5_13_1_2033 9 209 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 251 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 209 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 251 (accept_3_2 7 209 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 251
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 251 (accept_3_2 4 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 251 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 209 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 251 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 251 (accept_3_2 1 209 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 251))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 208 251 (Eq.refl
  Bool.true) (allA_of_3_0 44 208 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 207 251 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 251 (accept_3_2 43 207 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 207 251 (Polychromatic418967fa.accept_13_3_12_4_1_110 42 207 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 251
  (Polychromatic418967fa.accept_13_2_12_4_1_943 41 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 251 (accept_3_2 40 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 251 (Polychromatic418967fa.accept_16_7_15_11_1_951 39 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 251 (accept_3_2 37 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 251 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 207 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 251
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 35 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 207 251 (accept_3_2 34 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 207 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 207 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 251 (accept_3_2 31 207 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 251 (Polychromatic418967fa.accept_7_2_4_6_1_166
  30 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 251
  (Polychromatic418967fa.accept_13_3_12_4_1_110 29 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 251 (accept_3_2 28 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 251 (Polychromatic418967fa.accept_17_10_3_13_1_6639 27 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 251 (accept_3_2 25 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 207 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 251
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 251 (accept_3_2 22 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 251 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 251 (accept_3_2 19 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 251 (Polychromatic418967fa.accept_13_5_12_4_1_449 18 207 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 251
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 251 (accept_3_2 16 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 207 251 (Polychromatic418967fa.accept_13_2_12_4_1_943 15 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 251 (accept_3_2 13 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 251 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 251 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 251
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 207 251 (accept_3_2 10 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 207 251 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 207 251 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 251
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 251 (accept_3_2 7 207 251
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 251 (Polychromatic418967fa.accept_10_6_7_1_1_1297
  6 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 251
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 251 (accept_3_2 4 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 251 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 251 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 251 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 251 (accept_3_2 1 207 251 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 251)))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_251_segment_001))))))))))))))))))))))))))))))))))))))))))))


