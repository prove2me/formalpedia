-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch249
-- name    : Polychromatic418967fa_Branch249
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:28:48.287513+00:00
-- url     : https://prove2.me/theorems/a6823acb-256d-4a2b-b510-11a6cb39d763
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch249_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_249 : allB 249 249 :=
  allB_succ' 2 248 249 (Eq.refl Bool.true) (allA_succ_of_accept 1 248 249 (accept_3_4 1 248 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 248 249)) (allB_succ' 3 247 249 (Eq.refl Bool.true) (allA_succ_of_accept 2 247 249
  (accept_3_5 2 247 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 249
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 247 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 247 249))) (allB_succ' 4 246 249 (Eq.refl Bool.true) (allA_succ_of_gcd 3 246 249 3 1 82 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 246 249
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 246 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 246 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 246 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 246 249)))) (allB_succ' 5 245 249 (Eq.refl Bool.true) (allA_succ_of_accept 4
  245 249 (accept_3_4 4 245 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 249
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 245 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 245 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 245 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 249 (accept_3_4 1 245 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 245 249))))) (allB_succ' 6 244 249 (Eq.refl Bool.true) (allA_succ_of_accept 5 244 249
  (accept_3_5 5 244 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 244 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 244 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 244 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 244 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 249 (accept_3_5 2 244 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 244 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 244 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 249)))))) (allB_succ' 7 243 249 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 243 249 3 2 81 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 243 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 243 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 249 (Polychromatic418967fa.accept_10_4_3_9_1_1262 4 243 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 249 3 1 81 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 243 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 249))))))) (allB_succ' 8 242 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 242 249 (accept_3_4 7 242 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  242 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 242 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 242 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 242 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 249 (accept_3_4 4 242 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 242 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 249 (accept_3_4 1 242 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  249)))))))) (allB_succ' 9 241 249 (Eq.refl Bool.true) (allA_succ_of_accept 8 241 249 (accept_3_5 8 241 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 249 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 241
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 241 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 249 (accept_3_5 5 241 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 241 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 241 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 249 (accept_3_5 2 241 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 241 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 249))))))))) (allB_succ' 10 240 249 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 240 249 3 3 80 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 240 249 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 240 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 249 (Polychromatic418967fa.accept_21_7_9_18_1_7519
  7 240 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 249 3 2 80 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 240 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 240 249 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 240 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 240 249 3 1 80 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 240 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 2 240 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 249
  (Polychromatic418967fa.accept_13_1_6_2_1_377 1 240 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 249)))))))))) (allB_succ' 11 239 249 (Eq.refl Bool.true) (allA_succ_of_accept 10 239 249 (accept_3_4 10
  239 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 249
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 239 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 239 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 239 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 249 (accept_3_4 7 239 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 239 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 239 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  239 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 249 (accept_3_4 4 239
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 239 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 239 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 239 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 249 (accept_3_4 1 239 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 239 249))))))))))) (allB_succ' 12 238 249 (Eq.refl Bool.true) (allA_succ_of_accept 11 238 249
  (accept_3_5 11 238 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 238 249
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 238 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 238 249 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 238 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 238 249 (accept_3_5 8 238 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 238 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 238 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 238 249 (Polychromatic418967fa.accept_12_6_10_9_1_531
  6 238 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 238 249 (accept_3_5 5
  238 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 249
  (Polychromatic418967fa.accept_10_4_8_9_1_784 4 238 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 238 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 238 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 249 (accept_3_5 2 238 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 238 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 238 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 249)))))))))))) (allB_succ' 13 237 249 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 237 249 3 4 79 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 237 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 237 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 237 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 237 249 3 3 79 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 237 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 237 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 249 3 2 79 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 237 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 237 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 237 249 3 1 79 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 237 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 237 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 237 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 249))))))))))))) (allB_succ' 14 236 249
  (Eq.refl Bool.true) (allA_succ_of_accept 13 236 249 (accept_3_4 13 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 236 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 236 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 236 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 236 249 (accept_3_4 10 236 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 236 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  236 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 236 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 236 249 (accept_3_4 7 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  236 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 236 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 236 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 249 (accept_3_4 4 236 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 236 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 236 249 (accept_3_4 1 236 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  249)))))))))))))) (allB_succ' 15 235 249 (Eq.refl Bool.true) (allA_succ_of_accept 14 235 249 (accept_3_5 14 235 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 249 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 249
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 249 (accept_3_5 11 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 249 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 235 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 249 (accept_3_5 8 235 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 235 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 249 (accept_3_5 5 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 235 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 235 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 249 (accept_3_5 2 235 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 235 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 249))))))))))))))) (allB_succ' 16 234 249 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 234 249 3 5 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 234 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 234 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 234 249 (Polychromatic418967fa.accept_7_6_3_4_1_294
  13 234 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 234 249 3 4 78 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 234 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 234 249 (Polychromatic418967fa.accept_11_10_3_7_1_2564 10 234 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 234 249 3 3 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 234 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 234 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 234 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 249 3 2 78 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 5 234 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 249 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 234 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 234 249 3 1 78 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 234 249
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 234 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 234 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 234 249)))))))))))))))) (allB_succ' 17 233 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 233 249 (accept_3_4 16 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 249 (accept_3_4 13 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 233 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 233 249 (accept_3_4 10 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  233 249 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 233 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 249 (accept_3_4 7 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 233 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 249 (accept_3_4 4 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 233 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 249 (accept_3_4 1 233 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 249))))))))))))))))) (allB_succ' 18 232 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 232 249 (accept_3_5 17 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 232 249 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 232 249 (Polychromatic418967fa.accept_16_15_8_9_1_2563 15 232 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 232 249 (accept_3_5 14 232 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 232 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 232 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 232 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 232 249 (accept_3_5 11 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 232 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 232 249 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 232 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 249 (accept_3_5 8 232 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 232 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 232 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 249
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 232 249 (accept_3_5 5 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  232 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 232 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 232 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 232 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 249 (accept_3_5 2 232 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 232 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 232 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 249)))))))))))))))))) (allB_succ' 19 231 249
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 231 249 3 6 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 231 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 231 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 249
  (Polychromatic418967fa.accept_13_3_10_2_1_381 16 231 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 231 249 3 5 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 231 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 231 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 231
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 231 249 3 4 77 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 231 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 231 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 231 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 231 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 249 3 3 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 8 231 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 231 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 231 249 3 2 77 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 231 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 5 231 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 249 (Polychromatic418967fa.accept_14_4_7_11_1_790 4 231 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 249 3 1 77 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 231 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 249))))))))))))))))))) (allB_succ' 20 230 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 230 249 (accept_3_4 19 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 230 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 230 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 230 249 (accept_3_4 16 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 230 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 230 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 230 249
  (Polychromatic418967fa.accept_11_3_10_7_1_129 14 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 230 249 (accept_3_4 13 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 230 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 230 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 230 249 (accept_3_4 10 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 230 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 230 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 230 249 (accept_3_4 7 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  230 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 230 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 249 (accept_3_4 4 230 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 230 249 (accept_3_4 1 230 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  249)))))))))))))))))))) (allB_succ' 21 229 249 (Eq.refl Bool.true) (allA_succ_of_accept 20 229 249 (accept_3_5 20 229
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 249 (Polychromatic418967fa.accept_9_1_4_6_1_5
  19 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 249
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 249 (accept_3_5 17 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 249 (accept_3_5 14 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 229 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 249 (accept_3_5 11 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 249 (accept_3_5 8 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 229 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 249 (accept_3_5 5 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 229 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 249 (accept_3_5 2 229 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 229 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 249))))))))))))))))))))) (allB_succ' 22 228 249
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 228 249 3 7 76 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 228 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 228 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 249
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 249 3 6 76 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 228 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 228 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 228 249 3 5 76 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 228 249
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 228 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 249 3 4 76 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 249
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 228 249 3 3 76 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 228 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 228 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 228 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 249 3 2 76 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 249
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 228 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 228 249 3 1 76 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 228 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 249
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 228 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 249)))))))))))))))))))))) (allB_succ' 23 227 249 (Eq.refl Bool.true) (allA_succ_of_accept 22 227 249
  (accept_3_4 22 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 249
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 227 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 227 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 249 (accept_3_4 19 227 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 227 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 249 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 249 (accept_3_4 16
  227 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 227 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 249 (accept_3_4 13 227 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 227 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 249
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 249 (accept_3_4 10 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 249 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 249 (accept_3_4 7 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 249 (accept_3_4 4 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 227 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 249 (accept_3_4 1 227 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 249))))))))))))))))))))))) (allB_succ' 24 226 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 226 249 (accept_3_5 23 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 249 (accept_3_5 20 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 226 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 249
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 226 249 (accept_3_5 17 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 249 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 249 (accept_3_5 14 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 226 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 249 (accept_3_5 11 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 249 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 249 (accept_3_5 8 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 249 (accept_3_5 5 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 226 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 249 (accept_3_5 2 226 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 226 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 249)))))))))))))))))))))))) (allB_succ' 25 225 249
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 225 249 3 8 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 225 249 (Polychromatic418967fa.accept_17_6_4_11_1_4072 23 225 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 249
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 22 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 225 249 3 7 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 225 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 20 225 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 225 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 225 249 3 6 75 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 225 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 225 249 (Polychromatic418967fa.accept_10_6_5_9_1_1233 16 225 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 249 3 5 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231
  14 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 249
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 225 249 3 4 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 225 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 11 225 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 225 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 225 249 3 3 75 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 249
  (Polychromatic418967fa.accept_16_8_1_9_1_847 8 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 249 (Polychromatic418967fa.accept_19_7_16_2_1_6953 7 225 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 249 3 2 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 225 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 249
  (Polychromatic418967fa.accept_10_4_5_9_1_1231 4 225 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 249 3 1 75 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 249 (Polychromatic418967fa.accept_16_2_1_9_1_2577 2 225 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 249 (Polychromatic418967fa.accept_10_1_5_9_1_157 1 225 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 249))))))))))))))))))))))))) (allB_succ' 26
  224 249 (Eq.refl Bool.true) (allA_succ_of_accept 25 224 249 (accept_3_4 25 224 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 224 249 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 224 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 224 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 224 249 (accept_3_4 22 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 224 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 224 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 20 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 249 (accept_3_4 19 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 224 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 224 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 224 249 (accept_3_4 16 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 224 249 (Polychromatic418967fa.accept_10_5_4_9_1_420 15 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 224 249 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 249 (accept_3_4 13 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 224 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 224 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 224 249 (accept_3_4 10 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  224 249 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 224 249 (Polychromatic418967fa.accept_10_8_4_9_1_1229 8 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 249 (accept_3_4 7 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 224 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 224 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 224 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 224 249 (accept_3_4 4 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  224 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 224 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 224 249 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 249 (accept_3_4 1 224 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 249)))))))))))))))))))))))))) (allB_succ' 27 223 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 223 249 (accept_3_5 26 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 249 (Polychromatic418967fa.accept_17_8_2_11_1_4069 25 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 249 (accept_3_5 23 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 223 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 249 (accept_3_5 20 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 249 (accept_3_5 17 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 223 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 249
  (Polychromatic418967fa.accept_11_4_3_7_1_828 15 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 249 (accept_3_5 14 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 223 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 249 (accept_3_5 11 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 249 (accept_3_5 8 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 249 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 249 (accept_3_5 5 223 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 249
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 249 (accept_3_5 2 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 223 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 249))))))))))))))))))))))))))) (allB_succ' 28 222 249 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 222 249 3 9 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 222 249 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 249 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 222
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 222 249 3 8 74 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 222 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 222 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 222 249 3 7 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 222 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 222 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 249 3 6 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 222 249 (Polychromatic418967fa.accept_10_7_2_9_1_775 17 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 222 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 222 249 3 5 74 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 222 249
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 222 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 249 3 4 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 249
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 222 249 3 3 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 222 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 222 249 3 2 74 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 222 249
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 222 249 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 222 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 249 3 1 74 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 222 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 222 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 222 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 249)))))))))))))))))))))))))))) (allB_succ' 29 221 249 (Eq.refl Bool.true) (allA_succ_of_accept 28 221
  249 (accept_3_4 28 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 249
  (Polychromatic418967fa.accept_12_3_5_9_1_176 27 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 221 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 221 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 221 249 (accept_3_4 25 221 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 221 249 (Polychromatic418967fa.accept_18_6_5_15_1_7292 24 221 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 221 249
  (Polychromatic418967fa.accept_16_7_13_9_1_1653 23 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 221 249 (accept_3_4 22 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 249 (accept_3_4 19 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 249 (Polychromatic418967fa.accept_10_8_1_9_1_413 18 221 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 249
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 249 (accept_3_4 16 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 249 (Polychromatic418967fa.accept_10_5_1_9_1_791 15 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 249 (accept_3_4 13 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 221 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 249
  (Polychromatic418967fa.accept_9_2_5_6_1_536 11 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 221 249 (accept_3_4 10 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  221 249 (Polychromatic418967fa.accept_18_9_5_15_1_2246 9 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 221 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 249 (accept_3_4 7 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 249 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 221 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 5 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 249 (accept_3_4 4 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 221 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 249 (accept_3_4 1 221 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 249))))))))))))))))))))))))))))) (allB_succ' 30 220 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 220 249 (accept_3_5 29 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 220 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 220 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 220 249 (accept_3_5 26 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 220 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 220 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 220 249
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 24 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 220 249 (accept_3_5 23 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 220 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 220 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 220 249 (accept_3_5 20 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 220 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 220 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 220 249
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 220 249 (accept_3_5 17 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 220 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 220 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 220 249 (accept_3_5 14 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 220 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 220 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 220 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 220 249 (accept_3_5 11 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 220 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 220 249 (Polychromatic418967fa.accept_18_9_4_15_1_555 9 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 220 249 (accept_3_5 8 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 220 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 220 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 220 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 220 249 (accept_3_5 5 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  220 249 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 220 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 220 249 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 249 (accept_3_5 2 220 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 220 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 249)))))))))))))))))))))))))))))) (allB_succ' 31 219
  249 (Eq.refl Bool.true) (allA_succ_of_gcd 30 219 249 3 10 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 219 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 219 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 249
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 219 249 3 9 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 219 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 219 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 219 249 3 8 73 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 219 249
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 219 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 219 249 3 7 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 219 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20
  219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 219 249 3 6 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 219 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 219 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 249 3 5 73 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 249 3 4 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 219 249 3 3 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 219 249 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 219 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 249 3 2 73 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 219 249 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 219 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 249 3 1 73 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 249
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 219 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 219 249))))))))))))))))))))))))))))))) (allB_succ' 32 218 249 (Eq.refl Bool.true) (allA_succ_of_accept 31
  218 249 (accept_3_4 31 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 218 249
  (Polychromatic418967fa.accept_9_3_2_6_1_264 30 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 218 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 218 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 249 (accept_3_4 28 218 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 218 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 249 (Polychromatic418967fa.accept_7_5_1_4_1_122
  26 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 218 249 (accept_3_4 25
  218 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 218 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 218 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 218 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 249 (accept_3_4 22 218 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 218 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 218 249
  (Polychromatic418967fa.accept_17_3_14_11_1_5243 20 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 218 249 (accept_3_4 19 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 218 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 218 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 218 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 218 249 (accept_3_4 16 218 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 218 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15
  218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 218 249
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 218 249 (accept_3_4 13 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 218 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 218 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 218 249 (accept_3_4 10 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 218 249 (Polychromatic418967fa.accept_21_9_8_18_1_7516 9 218 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 218 249
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 218 249 (accept_3_4 7 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  218 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 218 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 218 249 (accept_3_4 4 218 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 218 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 249
  (Polychromatic418967fa.accept_11_2_9_7_1_124 2 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 218 249 (accept_3_4 1 218 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  249)))))))))))))))))))))))))))))))) (allB_succ' 33 217 249 (Eq.refl Bool.true) (allA_succ_of_accept 32 217 249
  (accept_3_5 32 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 217 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 249 (accept_3_5 29 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 217 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 217 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 249 (Polychromatic418967fa.accept_12_3_1_9_1_202
  27 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 249 (accept_3_5 26
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 25 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 217 249 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 249 (accept_3_5 23 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 217 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 217 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 249 (accept_3_5 20
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 249
  (Polychromatic418967fa.accept_13_6_9_2_1_838 19 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 217 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 18 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 249 (accept_3_5 17 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 217 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 217 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 249 (Polychromatic418967fa.accept_11_4_8_7_1_819
  15 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 249 (accept_3_5 14
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 217 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 249 (accept_3_5 11 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 217 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 217 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 249 (Polychromatic418967fa.accept_21_9_7_18_1_1780
  9 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 249 (accept_3_5 8
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 249
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 217 249 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 249 (accept_3_5 5 217 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 217 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 217 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3
  217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 249 (accept_3_5 2 217
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 249
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 217 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 217 249))))))))))))))))))))))))))))))))) (allB_succ' 34 216 249 (Eq.refl Bool.true) (allA_succ_of_gcd 33 216
  249 3 11 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  216 249 (Polychromatic418967fa.accept_13_6_8_2_1_1484 32 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 216 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 216 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 249 3 10 72 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 249
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 29 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 216 249 (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 216 249 3 9 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 216 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 249
  (Polychromatic418967fa.accept_10_5_6_9_1_2235 25 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 249 3 8 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 216 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 216 249 (Polychromatic418967fa.accept_23_22_9_19_1_15071 22
  216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 216 249 3 7 72 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 216 249
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 216 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 249 3 6 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 17
  216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 216 249 3 5 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 216 249 (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 249 (Polychromatic418967fa.accept_10_3_6_9_1_779 13 216
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 249 3 4 72 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 249
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 216 249 3 3 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 216 249 (Polychromatic418967fa.accept_22_8_18_7_1_7141 8 216 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 249
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 249 3 2 72 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 249 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 216 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 216 249 3 1 72 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 216 249
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 216 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 249 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 216 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 249)))))))))))))))))))))))))))))))))) (allB_succ' 35 215 249 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 215 249 (accept_3_4 34 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 215 249 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 215 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 215 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 249 (accept_3_4 31 215 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 249 (accept_3_4 28 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 249 (accept_3_4 25 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 215 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 249 (accept_3_4 22 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 249 (accept_3_4 19 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 249
  (Polychromatic418967fa.accept_31_17_29_1_1_15070 17 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 215 249 (accept_3_4 16 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 215 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 215 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 249 (accept_3_4 13 215 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12
  215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 249 (accept_3_4 10 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 249 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 249 (accept_3_4 7 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 5 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 249 (accept_3_4 4 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 215 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 249 (accept_3_4 1 215 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 249))))))))))))))))))))))))))))))))))) (allB_succ' 36 214 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 214 249 (accept_3_5 35 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 214 249 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 214 249 (Polychromatic418967fa.accept_10_3_4_9_1_15 33 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 249 (accept_3_5 32 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 214 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 214 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 214 249 (accept_3_5 29 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 214 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 214 249 (accept_3_5 26 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 214 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 214 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 214 249
  (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 214 249 (accept_3_5 23 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 214 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 214 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 214 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 214 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 214 249 (accept_3_5 20 214 249
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 214 249
  (Polychromatic418967fa.accept_10_8_4_9_1_1229 18 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 214 249 (accept_3_5 17 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 214 249 (Polychromatic418967fa.accept_19_16_5_2_1_8375 16 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 214 249 (accept_3_5 14 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 214 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 214 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 214 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 214 249 (accept_3_5 11 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 214 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 214 249 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 214 249 (accept_3_5 8 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 214 249
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 214 249 (accept_3_5 5 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  214 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 214 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 214 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 249 (accept_3_5 2 214 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 214 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 249)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 213 249 (Eq.refl Bool.true) (allA_succ_of_gcd 36 213 249 3 12 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 213 249 (Polychromatic418967fa.accept_13_9_5_2_1_2185
  35 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 34 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 213 249 3 11 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 213 249 (Polychromatic418967fa.accept_21_11_3_18_1_3068 32 213 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 249
  (Polychromatic418967fa.accept_19_12_4_2_1_4121 31 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 213 249 3 10 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 213 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 213 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 249 (Polychromatic418967fa.accept_8_4_5_1_1_299
  28 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 249 3 9 71 83
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 249
  (Polychromatic418967fa.accept_10_6_3_9_1_1207 26 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 213 249 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 213 249 3 8 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 213 249 (Polychromatic418967fa.accept_13_10_5_2_1_1477
  23 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 213 249 3 7 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 213 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 249 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 213
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 249 3 6 71 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 249
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 249 (Polychromatic418967fa.accept_10_6_3_9_1_1207 16 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 213 249 3 5 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 249 (Polychromatic418967fa.accept_10_4_3_9_1_1262
  14 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 213 249 3 4 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 213 249 (Polychromatic418967fa.accept_16_11_5_9_1_1617 11 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 249 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 213
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 249 3 3 71 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 213 249 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 249 3 2 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 249 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 213 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 249
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 213 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 213 249 3 1 71 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 213 249 (Polychromatic418967fa.accept_17_2_9_11_1_4057 2 213 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 213 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 249)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 212 249 (Eq.refl Bool.true) (allA_succ_of_accept 37 212 249 (accept_3_4 37 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 212 249 (Polychromatic418967fa.accept_17_2_8_11_1_1041 36 212 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 212 249 (accept_3_4 34 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 212 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 212 249 (Polychromatic418967fa.accept_11_10_3_7_1_2564 32 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 212 249 (accept_3_4 31 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 212 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 212 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 212 249 (accept_3_4 28 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 212 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 212 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 249 (accept_3_4 25 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 212 249 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 212 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 212 249 (accept_3_4 22 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 212 249 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 212 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 249 (accept_3_4 19 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 212 249 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 212 249 (accept_3_4 16 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 212 249 (Polychromatic418967fa.accept_11_4_3_7_1_828 15 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 212 249 (Polychromatic418967fa.accept_16_14_4_9_1_1646 14 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 249 (accept_3_4 13 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 212 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 249 (accept_3_4 10 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 249 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 249 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 249 (accept_3_4 7 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 212 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 249
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 249 (accept_3_4 4 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 249 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 212 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 249 (Polychromatic418967fa.accept_9_2_5_6_1_536 2 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 249 (accept_3_4 1 212 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 212 249)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 211 249 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 211 249 (accept_3_5 38 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 211 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 211 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 249 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 211
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 211 249 (accept_3_5 35 211
  249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2
  34 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 249
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 211 249 (accept_3_5 32 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 211 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 249 (accept_3_5 29 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 211 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 211 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 249
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 27 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 249 (accept_3_5 26 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 249 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 249 (accept_3_5 23 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 249
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 249 (accept_3_5 20 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 249 (accept_3_5 17 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 211 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 249
  (Polychromatic418967fa.accept_10_5_1_9_1_791 15 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 249 (accept_3_5 14 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 249 (Polychromatic418967fa.accept_17_13_7_11_1_3985 13 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 249 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 249 (accept_3_5 11 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 249
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 249 (accept_3_5 8 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 249 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 249 (accept_3_5 5 211 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 211 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 249
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 249 (accept_3_5 2 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 249 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 211 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 249))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 210 249 (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 210 249 3 13 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 210 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 210 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 249 3 12 70 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 210 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 210 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 210 249 3 11 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 210 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 32
  210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 249
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 249 3 10 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 210 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 210 249 3 9 70 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 210 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 210 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 210 249 3 8 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 210 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 210 249 3 7 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 210 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 249 3 6 70 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 210 249 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 210 249 3 5 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 210 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 249 3 4 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 210 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 210 249 3 3 70 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 210 249
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 210 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 249 3 2 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 249 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 210 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 210 249
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 210 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 210 249 3 1 70 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 210 249 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 210 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 249 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 210 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 249))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 209 249 (Eq.refl Bool.true) (allA_succ_of_accept 40 209 249 (accept_3_4 40 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 249 (accept_3_4 37 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 249 (Polychromatic418967fa.accept_15_6_14_9_1_1471 36 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 249 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 249 (accept_3_4 34 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 209 249 (accept_3_4 31 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 209 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 209 249 (Polychromatic418967fa.accept_13_3_1_2_1_2960 29 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 249 (accept_3_4 28 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 209
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 209 249 (accept_3_4 25 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 209 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 209 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 249 (accept_3_4 22 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 249 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 209 249 (accept_3_4 19 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 209 249 (Polychromatic418967fa.accept_16_2_1_9_1_2577 18 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 209 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 209 249 (accept_3_4 16 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 209 249 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 209 249 (accept_3_4 13 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 209 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 249 (Polychromatic418967fa.accept_21_11_20_18_1_7656 11 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 249 (accept_3_4 10 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 249 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 209 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 249 (accept_3_4 7 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 249 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 249 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 249 (accept_3_4 4 209 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 249 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 209 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 249
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 249 (accept_3_4 1 209 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  249))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 208 249 (Eq.refl Bool.true) (allA_succ_of_accept 41 208
  249 (accept_3_5 41 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 249
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 208 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 208 249 (accept_3_5 38 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 208 249 (Polychromatic418967fa.accept_7_1_5_4_1_134
  36 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 249 (accept_3_5 35
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 34 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 208 249 (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 208 249 (accept_3_5 32 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 208 249 (Polychromatic418967fa.accept_7_2_5_4_1_115
  30 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 249 (accept_3_5 29
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 249
  (Polychromatic418967fa.accept_19_9_18_2_1_8383 28 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 208 249 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 208 249 (accept_3_5 26 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 208 249 (Polychromatic418967fa.accept_10_4_8_9_1_784
  24 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 249 (accept_3_5 23
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 249
  (Polychromatic418967fa.accept_7_1_5_4_1_134 22 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 208 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 208 249 (accept_3_5 20 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 208 249 (Polychromatic418967fa.accept_12_6_4_9_1_544
  18 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 249 (accept_3_5 17
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 249
  (Polychromatic418967fa.accept_7_2_5_4_1_115 16 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 208 249 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 249 (accept_3_5 14 208 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 12
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 249 (accept_3_5 11
  208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 249
  (Polychromatic418967fa.accept_17_10_4_11_1_4047 10 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 208 249 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 249 (accept_3_5 8 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 208 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 249
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 249 (accept_3_5 5 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 249 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 208 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 249 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 249 (accept_3_5 2 208 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 249 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 249))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 207 249 (Eq.refl Bool.true) (allA_succ_of_gcd 42 207 249 3 14 69 83 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 207 249
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 249 (Polychromatic418967fa.accept_13_1_12_2_1_384 40 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 207 249 3 13 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 207 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 207 249 3 12 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 207 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 35 207 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 34
  207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 207 249 3 11 69 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 207 249
  (Polychromatic418967fa.accept_10_2_7_9_1_783 32 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 207 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 31 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 207 249 3 10 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 207 249 (Polychromatic418967fa.accept_12_5_3_9_1_541
  29 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 249
  (Polychromatic418967fa.accept_10_8_7_9_1_425 28 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 207 249 3 9 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 207 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 249 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 207
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 249 3 8 69 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 249
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 249 3 7 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 249 (Polychromatic418967fa.accept_15_5_12_9_1_2253
  20 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 249
  (Polychromatic418967fa.accept_12_7_3_9_1_999 19 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 207 249 3 6 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 207 249 (Polychromatic418967fa.accept_12_5_3_9_1_541 17 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 249 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 207
  249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 249 3 5 69 83 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 249 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 249 3 4 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 249 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  11 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 249
  (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 207 249 3 3 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 207 249 (Polychromatic418967fa.accept_10_8_7_9_1_425 8 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 249 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 207 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 249 3 2 69 83 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 249
  (Polychromatic418967fa.accept_11_5_9_7_1_411 5 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 249 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 207 249 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 249 3 1 69 83 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 249 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 249
  (Polychromatic418967fa.accept_12_1_3_9_1_174 1 207 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 207 249))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 206 249 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 206 249 (accept_3_4 43 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 206 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 249 (accept_3_4 40 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 206 249 (accept_3_4 37 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 206 249 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 249 (accept_3_4 34 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 206 249 (Polychromatic418967fa.accept_10_3_6_9_1_779 33 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 206 249 (accept_3_4 31 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 206 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 206 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 249 (accept_3_4 28 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 249
  (Polychromatic418967fa.accept_11_4_8_7_1_819 26 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 206 249 (accept_3_4 25 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 206 249 (Polychromatic418967fa.accept_19_5_16_2_1_1717 24 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 249 (accept_3_4 22 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 249
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 249 (accept_3_4 19 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 249 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 249 (accept_3_4 16 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 249
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 249 (accept_3_4 13 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 249 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 249 (accept_3_4 10 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 249 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 249
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 249 (accept_3_4 7 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 249 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 249 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 249 (accept_3_4 4 206 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 249 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 249
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 249 (accept_3_4 1 206 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  249)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 205 249 (Eq.refl Bool.true) (allA_succ_of_accept 44 205
  249 (accept_3_5 44 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 249
  (Polychromatic418967fa.accept_29_14_2_17_1_15069 43 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 205 249 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 249 (accept_3_5 41 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 205 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 205 249 (accept_3_5 38 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 205 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 205 249 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 249 (accept_3_5 35 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 205 249
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 205 249 (accept_3_5 32 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 205 249 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 205 249 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 205 249 (accept_3_5 29 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 205 249
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 205 249 (accept_3_5 26 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 205 249 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 205 249 (Polychromatic418967fa.accept_10_4_5_9_1_1231 24 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 205 249 (accept_3_5 23 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 205 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 205 249 (accept_3_5 20 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 205 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 205 249 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 249 (accept_3_5 17 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 205 249
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 249
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 249 (accept_3_5 14 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 249 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 249 (accept_3_5 11 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 249
  (Polychromatic418967fa.accept_19_9_15_2_1_9758 9 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 249 (accept_3_5 8 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 249 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 249 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 249 (accept_3_5 5 205 249 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 249 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 249 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 249
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 249 (accept_3_5 2 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 249 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 205 249 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 249)))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_249_segment_002))))))))))))))))))))))))))))))))))))))))))))


