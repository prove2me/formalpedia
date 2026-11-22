-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch243
-- name    : Polychromatic418967fa_Branch243
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:27:42.324999+00:00
-- url     : https://prove2.me/theorems/a22c938e-e071-4bbe-ae41-1d461873953e
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch243_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_243 : allB 243 243 :=
  allB_succ' 2 242 243 (Eq.refl Bool.true) (allA_succ_of_accept 1 242 243 (accept_3_4 1 242 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 242 243)) (allB_succ' 3 241 243 (Eq.refl Bool.true) (allA_succ_of_accept 2 241 243
  (accept_3_5 2 241 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 241 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 241 243))) (allB_succ' 4 240 243 (Eq.refl Bool.true) (allA_succ_of_gcd 3 240 243 3 1 80 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 240 243
  (Polychromatic418967fa.accept_13_2_6_9_1_2636 2 240 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 240 243 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 240 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 240 243)))) (allB_succ' 5 239 243 (Eq.refl Bool.true) (allA_succ_of_accept 4
  239 243 (accept_3_4 4 239 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 239 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 239 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 239 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 243 (accept_3_4 1 239 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 239 243))))) (allB_succ' 6 238 243 (Eq.refl Bool.true) (allA_succ_of_accept 5 238 243
  (accept_3_5 5 238 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 238 243
  (Polychromatic418967fa.accept_19_4_10_15_1_9243 4 238 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 238 243 (Polychromatic418967fa.accept_19_3_10_15_1_9241 3 238 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 243 (accept_3_5 2 238 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 238 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 238 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 243)))))) (allB_succ' 7 237 243 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 237 243 3 2 79 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 237 243 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 237 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 237 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 237 243 3 1 79 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 237 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 237 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 237 243))))))) (allB_succ' 8 236 243 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 236 243 (accept_3_4 7 236 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  236 243 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 236 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 236 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 236 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 236 243 (accept_3_4 4 236 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 236 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187 3 236 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 236 243
  (Polychromatic418967fa.accept_19_2_8_15_1_2447 2 236 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 236 243 (accept_3_4 1 236 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  243)))))))) (allB_succ' 9 235 243 (Eq.refl Bool.true) (allA_succ_of_accept 8 235 243 (accept_3_5 8 235 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 243 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 235 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 243
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 235 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 243 (accept_3_5 5 235 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 235 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 243 (Polychromatic418967fa.accept_18_3_1_9_1_1929 3 235 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 243 (accept_3_5 2 235 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 235 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 243))))))))) (allB_succ' 10 234 243 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 234 243 9 1 26 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 234 243 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 234 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 243 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  234 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 243 3 2 78 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 234 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 234 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 234 243 3 1 78 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 234 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 234 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 243
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 234 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 243)))))))))) (allB_succ' 11 233 243 (Eq.refl Bool.true) (allA_succ_of_accept 10 233 243 (accept_3_4 10
  233 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 243
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 233 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 233 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 233 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 243 (accept_3_4 7 233 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 233 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 233 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 243 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  233 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 243 (accept_3_4 4 233
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 243
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 233 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 233 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 233 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 243 (accept_3_4 1 233 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 233 243))))))))))) (allB_succ' 12 232 243 (Eq.refl Bool.true) (allA_succ_of_accept 11 232 243
  (accept_3_5 11 232 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 232 243
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 232 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 232 243 (Polychromatic418967fa.accept_19_9_4_15_1_1415 9 232 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 243 (accept_3_5 8 232 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 232 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 232 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 6
  232 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 232 243 (accept_3_5 5 232
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 232 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 232 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 232 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 232 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 243 (accept_3_5 2 232 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 232 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 232 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 243)))))))))))) (allB_succ' 13 231 243 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 231 243 3 4 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 231 243 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 231 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 243 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 231
  243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 243 3 3 77 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 243
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 231 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 243 (Polychromatic418967fa.accept_19_7_3_15_1_2428 7 231 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 243 3 2 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 243 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 231 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 243
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 231 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 231 243 3 1 77 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 231 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 2 231 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 243 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 231 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 243))))))))))))) (allB_succ' 14 230 243
  (Eq.refl Bool.true) (allA_succ_of_accept 13 230 243 (accept_3_4 13 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 230 243 (Polychromatic418967fa.accept_17_12_9_5_1_799 12 230 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 230 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 230 243 (accept_3_4 10 230 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 230 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  230 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 230 243 (accept_3_4 7 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  230 243 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 230 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 230 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 243 (accept_3_4 4 230 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 243 (Polychromatic418967fa.accept_18_3_14_9_1_4264 3 230 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 243
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 230 243 (accept_3_4 1 230 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  243)))))))))))))) (allB_succ' 15 229 243 (Eq.refl Bool.true) (allA_succ_of_accept 14 229 243 (accept_3_5 14 229 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 243
  (Polychromatic418967fa.accept_17_13_8_5_1_3532 13 229 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 229 243 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 229 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 243 (accept_3_5 11 229 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 229 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 229 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 243 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  229 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 243 (accept_3_5 8 229
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 243
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 229 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 229 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 229 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 243 (accept_3_5 5 229 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 229 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 229 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 243 (Polychromatic418967fa.accept_13_3_8_9_1_1134
  3 229 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 243 (accept_3_5 2
  229 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 243
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 229 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 229 243))))))))))))))) (allB_succ' 16 228 243 (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 243 3 5 76 81
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 228 243
  (Polychromatic418967fa.accept_20_14_8_3_1_6011 14 228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 228 243 (Polychromatic418967fa.accept_7_6_4_5_1_314 13 228 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 243 3 4 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 243 (Polychromatic418967fa.accept_10_1_8_3_1_947
  11 228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 228 243
  (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 228 243 3 3 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 228 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 228 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 243 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 243 3 2 76 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 243
  (Polychromatic418967fa.accept_10_5_8_3_1_229 5 228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 243 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 228 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 228 243 3 1 76 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 228 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 243
  (Polychromatic418967fa.accept_7_1_4_5_1_35 1 228 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 243)))))))))))))))) (allB_succ' 17 227 243 (Eq.refl Bool.true) (allA_succ_of_accept 16 227 243
  (accept_3_4 16 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 243
  (Polychromatic418967fa.accept_7_1_3_5_1_33 15 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 227 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 227 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 243 (accept_3_4 13 227 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 227 243 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 227 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 243
  (Polychromatic418967fa.accept_17_11_6_5_1_3662 11 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 243 (accept_3_4 10 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 243 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 227 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 243 (accept_3_4 7 227 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 243 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 227 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 243
  (Polychromatic418967fa.accept_10_5_7_3_1_561 5 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 243 (accept_3_4 4 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 243 (Polychromatic418967fa.accept_13_3_6_9_1_1150 3 227 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 227 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 243 (accept_3_4 1 227 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 243))))))))))))))))) (allB_succ' 18 226 243 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 226 243 (accept_3_5 17 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 243 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 243 (Polychromatic418967fa.accept_13_2_5_9_1_610 15 226 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 243 (accept_3_5 14 226 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 226 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 243
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 226 243 (accept_3_5 11 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 226 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 226 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 226 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 226 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 243 (accept_3_5 8 226 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 243 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  226 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 243
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 243 (accept_3_5 5 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 243 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 226 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 243 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 226 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 243 (accept_3_5 2 226 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 226 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 243)))))))))))))))))) (allB_succ' 19 225 243
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 225 243 9 2 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 225 243 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 225 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 243
  (Polychromatic418967fa.accept_17_16_4_5_1_3626 16 225 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 225 243 3 5 75 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 225 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 225 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 243 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 225 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 243 3 4 75 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 243
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 225 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 225 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 225 243 9 1 25 27 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 243 (Polychromatic418967fa.accept_10_8_5_3_1_543 8 225 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 243
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 225 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 225 243 3 2 75 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 225 243 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 225 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 243 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 225 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 243 3 1 75 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 243
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 225 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 225 243 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 225 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 225 243))))))))))))))))))) (allB_succ' 20 224 243 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 224 243 (accept_3_4 19 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 224 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 224 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 243 (accept_3_4 16 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 224 243 (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 224 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 243
  (Polychromatic418967fa.accept_20_14_4_3_1_2006 14 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 224 243 (accept_3_4 13 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 224 243 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 224 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 243 (accept_3_4 10 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 243 (Polychromatic418967fa.accept_10_9_4_3_1_539 9 224 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 243
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 224 243 (accept_3_4 7 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  224 243 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 243 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 243 (accept_3_4 4 224 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 243 (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 224 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 243
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 2 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 243 (accept_3_4 1 224 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  243)))))))))))))))))))) (allB_succ' 21 223 243 (Eq.refl Bool.true) (allA_succ_of_accept 20 223 243 (accept_3_5 20 223
  243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 243
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 223 243 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 243 (accept_3_5 17 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 223 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 223 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 243 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 243 (accept_3_5 14
  223 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 243
  (Polychromatic418967fa.accept_11_2_3_1_1_244 13 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 223 243 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 243 (accept_3_5 11 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 223 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 223 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 243 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 243 (accept_3_5 8
  223 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 243
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 223 243 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 243 (accept_3_5 5 223 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 223 243 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 243 (Polychromatic418967fa.accept_13_3_2_9_1_1187
  3 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 243 (accept_3_5 2
  223 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 243
  (Polychromatic418967fa.accept_7_1_6_5_1_39 1 223 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 223 243))))))))))))))))))))) (allB_succ' 22 222 243 (Eq.refl Bool.true) (allA_succ_of_gcd 21 222 243 3 7 74
  81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 222 243
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 243 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 222 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 222 243 3 6 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 222 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 243
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 222 243 3 5 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 222 243 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 222 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 222 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 243 3 4 74 81 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 243
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 243 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 222 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 222 243 3 3 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 222 243 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 222 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 243
  (Polychromatic418967fa.accept_14_7_12_5_1_1861 7 222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 243 3 2 74 81 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 222 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 243 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 222 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 243 3 1 74 81 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 243
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 222 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 243 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 222 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 222 243)))))))))))))))))))))) (allB_succ' 23 221 243 (Eq.refl Bool.true)
  (allA_succ_of_accept 22 221 243 (accept_3_4 22 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 221 243 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 221 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 221 243 (accept_3_4 19 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 221 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 221 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 243
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 221 243 (accept_3_4 16 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 221 243 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 221 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 221 243 (accept_3_4 13 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 221 243 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 221 243 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 243
  (Polychromatic418967fa.accept_33_11_23_12_1_9999 11 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 221 243 (accept_3_4 10 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 221 243 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 221 243 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 243 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 243
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 243 (accept_3_4 7 221 243
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 243
  (Polychromatic418967fa.accept_19_5_12_15_1_9244 5 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 243 (accept_3_4 4 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 243 (Polychromatic418967fa.accept_19_3_12_15_1_568 3 221 243 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 243 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 243 (accept_3_4 1 221 243 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 243)))))))))))))))))))))))
  (Polychromatic418967fa.branch_243_segment_002))))))))))))))))))))))


