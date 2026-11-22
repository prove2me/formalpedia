-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch257
-- name    : Polychromatic418967fa_Branch257
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:31.709012+00:00
-- url     : https://prove2.me/theorems/947e0588-579c-4a05-95d3-395e77978c53
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch257_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_257 : allB 257 257 :=
  allB_succ' 2 256 257 (Eq.refl Bool.true) (allA_of_3_0 2 256 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  255 257 (Eq.refl Bool.true) (allA_succ_of_accept 2 255 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 255 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 257 (accept_3_2 1 255 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 257))) (allB_succ' 4 254 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 254 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 254 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 254 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 2 254 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 254 257 (accept_3_2 1 254 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254 257)))) (allB_succ' 5 253 257 (Eq.refl Bool.true) (allA_of_3_0
  5 253 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 252 257 (Eq.refl Bool.true) (allA_succ_of_accept 5
  252 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 252 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 252 257 (accept_3_2 4 252 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 252 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 252 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 252 257 (Polychromatic418967fa.accept_13_2_5_10_1_250 2 252 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 257 (accept_3_2 1 252 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 257)))))) (allB_succ' 7 251 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 251 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 251 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 257 (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 251
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 257 (accept_3_2 4 251 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  251 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 251 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 257 (accept_3_2 1 251 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251 257)))))))
  (allB_succ' 8 250 257 (Eq.refl Bool.true) (allA_of_3_0 8 250 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 249 257 (Eq.refl Bool.true) (allA_succ_of_accept 8 249 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 249 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 257 (accept_3_2 7 249 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 249 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6
  249 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 257
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 249 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 249 257 (accept_3_2 4 249 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  249 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 249 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 249 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 249 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 257 (accept_3_2 1 249 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 249 257))))))))) (allB_succ' 10 248 257 (Eq.refl Bool.true) (allA_succ_of_accept 9 248
  257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 248 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 248 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 248 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 248 257 (accept_3_2 7 248 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 248 257 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 248 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 248 257 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  5 248 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 257 (accept_3_2 4
  248 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 3 248 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 248 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 248 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 248 257 (accept_3_2 1 248 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 248 257)))))))))) (allB_succ' 11 247 257 (Eq.refl Bool.true) (allA_of_3_0 11 247 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 246 257 (Eq.refl Bool.true) (allA_succ_of_accept 11 246 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 246 257 (accept_3_2 10 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  246 257 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 246 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 246 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 257 (accept_3_2 7 246 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 246 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 246 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 246 257
  (Polychromatic418967fa.accept_16_5_6_1_1_2118 5 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 246 257 (accept_3_2 4 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  246 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 246 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 246 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 246 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 246 257 (accept_3_2 1 246 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 246 257)))))))))))) (allB_succ' 13 245 257 (Eq.refl Bool.true) (allA_succ_of_accept 12
  245 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 245 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 245 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 245 257 (accept_3_2 10 245 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 245 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 245 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 245 257 (accept_3_2 7 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  245 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 245 257 (Polychromatic418967fa.accept_22_5_3_15_1_15707 5 245 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 257 (accept_3_2 4 245 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 245 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 257
  (Polychromatic418967fa.accept_10_2_5_7_1_1124 2 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 257 (accept_3_2 1 245 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  257))))))))))))) (allB_succ' 14 244 257 (Eq.refl Bool.true) (allA_of_3_0 14 244 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 243 257 (Eq.refl Bool.true) (allA_succ_of_accept 14 243 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 257 (accept_3_2 13 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 243 257 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 243 257 (Polychromatic418967fa.accept_19_11_15_10_1_7406 11 243 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 257 (accept_3_2 10 243 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 243 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 243 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 243 257 (accept_3_2 7 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  243 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 243 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 243 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 257 (accept_3_2 4 243 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 243 257 (Polychromatic418967fa.accept_17_3_5_2_1_14381 3 243 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 257 (accept_3_2 1 243 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243
  257))))))))))))))) (allB_succ' 16 242 257 (Eq.refl Bool.true) (allA_succ_of_accept 15 242 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 242 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 242 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 242 257 (accept_3_2 13 242 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 242 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 242 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 242 257 (accept_3_2 10
  242 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 242 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 242 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 242 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 242 257 (accept_3_2 7 242 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 242 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 242 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 242 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 5
  242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 257 (accept_3_2 4 242
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 257 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 242 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 257 (accept_3_2 1 242 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  257)))))))))))))))) (allB_succ' 17 241 257 (Eq.refl Bool.true) (allA_of_3_0 17 241 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 240 257 (Eq.refl Bool.true) (allA_succ_of_accept 17 240 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 240 257 (accept_3_2 16 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 240 257 (Polychromatic418967fa.accept_13_2_6_10_1_2703 15 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 240 257 (Polychromatic418967fa.accept_19_14_12_10_1_3368 14 240 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 240 257 (accept_3_2 13 240 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 240 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 240 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 240 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 240 257 (accept_3_2 10 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  240 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 240 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 240 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 257 (accept_3_2 7 240 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 240 257 (Polychromatic418967fa.accept_19_6_12_10_1_4683 6 240 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 240 257
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 240 257 (accept_3_2 4 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  240 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 240 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 240 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 240 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 257 (accept_3_2 1 240 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 240 257)))))))))))))))))) (allB_succ' 19 239 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 239 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 239 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 239 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 257 (accept_3_2 16 239 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 257 (Polychromatic418967fa.accept_13_2_5_10_1_250
  15 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 239 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 239 257 (accept_3_2 13 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 239 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 239 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 239 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 257 (accept_3_2 10 239 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 257 (Polychromatic418967fa.accept_25_9_14_7_1_15706 9 239 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 257
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 239 257 (accept_3_2 7 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  239 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 239 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 239 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 239 257 (accept_3_2 4 239 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 239 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 239 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 239 257 (accept_3_2 1 239 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239
  257))))))))))))))))))) (allB_succ' 20 238 257 (Eq.refl Bool.true) (allA_of_3_0 20 238 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 237 257 (Eq.refl Bool.true) (allA_succ_of_accept 20 237 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 257 (accept_3_2 19 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 237 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 237 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 237 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 257 (accept_3_2 16 237 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 237 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 237 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 257 (accept_3_2 13 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 237 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 237 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 257 (accept_3_2 10 237 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 257 (Polychromatic418967fa.accept_16_9_13_1_1_3069 9 237 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 257 (accept_3_2 7 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  237 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 237 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 237 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 257 (accept_3_2 4 237 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 237 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 237 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 257 (accept_3_2 1 237 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237
  257))))))))))))))))))))) (allB_succ' 22 236 257 (Eq.refl Bool.true) (allA_succ_of_accept 21 236 257
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 236 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 236 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 257 (accept_3_2 19 236 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 236 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 236 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 236 257 (accept_3_2 16 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 236 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 236 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 236 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 257 (accept_3_2 13 236 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 236 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 236 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 257
  (Polychromatic418967fa.accept_10_1_6_7_1_710 11 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 257 (accept_3_2 10 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 236 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 257 (accept_3_2 7 236 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 236 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 257 (accept_3_2 4 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 236 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 257 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 236 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 257 (accept_3_2 1 236 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 257)))))))))))))))))))))) (allB_succ' 23 235 257 (Eq.refl Bool.true) (allA_of_3_0
  23 235 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 234 257 (Eq.refl Bool.true) (allA_succ_of_accept 23
  234 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 234 257 (accept_3_2 22 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 234 257 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 234 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 234 257 (Polychromatic418967fa.accept_19_1_6_10_1_3366 20 234
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 257 (accept_3_2 19 234
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 234 257
  (Polychromatic418967fa.accept_11_7_3_4_1_729 18 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 234 257 (Polychromatic418967fa.accept_25_17_9_7_1_15705 17 234 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 257 (accept_3_2 16 234 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 234 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 234 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 234 257
  (Polychromatic418967fa.accept_19_14_6_10_1_11678 14 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 234 257 (accept_3_2 13 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 234 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 234 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 234 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 234 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 257 (accept_3_2 10 234 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 234 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9
  234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 234 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 8 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 234 257 (accept_3_2 7 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  234 257 (Polychromatic418967fa.accept_17_6_13_2_1_4549 6 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 234 257 (Polychromatic418967fa.accept_25_5_9_7_1_15704 5 234 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 234 257 (accept_3_2 4 234 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 234 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 234 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 234 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 234 257 (accept_3_2 1 234 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 234
  257)))))))))))))))))))))))) (allB_succ' 25 233 257 (Eq.refl Bool.true) (allA_succ_of_accept 24 233 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 233 257 (Polychromatic418967fa.accept_17_6_12_2_1_10966 23 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 257 (accept_3_2 22 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 233 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 233 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 233 257 (accept_3_2 19 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 233 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 233 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 257 (accept_3_2 16 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 233 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 233 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 257
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 14 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 257 (accept_3_2 13 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 257 (accept_3_2 10 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 257 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 233 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 257
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 257 (accept_3_2 7 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 257 (accept_3_2 4 233 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 233 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 257 (accept_3_2 1 233 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  257))))))))))))))))))))))))) (allB_succ' 26 232 257 (Eq.refl Bool.true) (allA_of_3_0 26 232 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 231 257 (Eq.refl Bool.true) (allA_succ_of_accept 26 231 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 231 257 (accept_3_2 25 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 231 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 231 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 231 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 257 (accept_3_2 22 231 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 231 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 231 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 231 257 (accept_3_2 19 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 231 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 231 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 231 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 257 (accept_3_2 16 231 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 257 (Polychromatic418967fa.accept_17_15_10_2_1_2309 15 231 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 231 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 257 (accept_3_2 13 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 231 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 231 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 231 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 257 (accept_3_2 10 231 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 231 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 231 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 257 (accept_3_2 7 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  231 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 231 257 (Polychromatic418967fa.accept_19_5_3_10_1_4641 5 231 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 257 (accept_3_2 4 231 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 231 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 231 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 257 (accept_3_2 1 231 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231
  257))))))))))))))))))))))))))) (allB_succ' 28 230 257 (Eq.refl Bool.true) (allA_succ_of_accept 27 230 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 230 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 26 230 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 257 (accept_3_2 25 230 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 230 257 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 230 257 (accept_3_2 22 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 230 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 230 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 257 (accept_3_2 19 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 230 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 257
  (Polychromatic418967fa.accept_19_17_2_10_1_8940 17 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 230 257 (accept_3_2 16 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 230 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 230 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 230 257 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 230
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 257 (accept_3_2 13 230
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 257
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 230 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 230 257 (accept_3_2 10 230 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 230 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 230 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 230 257 (accept_3_2 7 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  230 257 (Polychromatic418967fa.accept_13_6_9_10_1_1201 6 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 230 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 230 257 (accept_3_2 4 230 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 230 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 230 257
  (Polychromatic418967fa.accept_16_2_6_1_1_2069 2 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 230 257 (accept_3_2 1 230 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  257)))))))))))))))))))))))))))) (allB_succ' 29 229 257 (Eq.refl Bool.true) (allA_of_3_0 29 229 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 228 257 (Eq.refl Bool.true) (allA_succ_of_accept 29 228 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 228 257 (accept_3_2 28 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 228 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 228 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 257 (accept_3_2 25 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 228 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 228 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 228 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 228 257 (accept_3_2 22 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 228 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 228 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 228 257 (accept_3_2 19 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 228 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 228 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 228 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 228 257 (accept_3_2 16 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 228 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 228 257 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 228 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 257 (accept_3_2 13 228 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 228 257 (Polychromatic418967fa.accept_11_1_8_4_1_717 12 228
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 228 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 257 (accept_3_2 10 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  228 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 228 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 257 (accept_3_2 7 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 228 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 228 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 228 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 228 257 (accept_3_2 4 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  228 257 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 228 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 228 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 228 257 (accept_3_2 1 228 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 228 257)))))))))))))))))))))))))))))) (allB_succ' 31 227 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 227 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 227 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 257 (accept_3_2 28 227 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 227 257
  (Polychromatic418967fa.accept_19_8_18_10_1_3360 27 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 257 (accept_3_2 25 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 227 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 257 (accept_3_2 22 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 257 (Polychromatic418967fa.accept_16_4_3_1_1_8843 20 227 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 257 (accept_3_2 19 227 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 257 (accept_3_2 16 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 257 (accept_3_2 13 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 227 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 257
  (Polychromatic418967fa.accept_19_11_18_10_1_1148 11 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 227 257 (accept_3_2 10 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 227 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 227 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 227 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 257 (accept_3_2 7 227 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 257
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 257 (accept_3_2 4 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 227 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 257 (accept_3_2 1 227 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 257))))))))))))))))))))))))))))))) (allB_succ' 32 226 257 (Eq.refl Bool.true)
  (allA_of_3_0 32 226 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 225 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 225 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 257 (accept_3_2 31 225 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 225 257 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 225 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 225 257
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 29 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 225 257 (accept_3_2 28 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 225 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 257 (accept_3_2 25 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 225 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 225 257
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 257 (accept_3_2 22 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 225 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 257 (accept_3_2 19 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 225 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 225 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 225 257 (accept_3_2 16 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 225 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 257 (accept_3_2 13 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 225 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 225 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 225 257 (accept_3_2 10 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  225 257 (Polychromatic418967fa.accept_17_9_4_2_1_2298 9 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 257 (accept_3_2 7 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 225 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 225 257
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 5 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 257 (accept_3_2 4 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  225 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 225 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 225 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 257 (accept_3_2 1 225 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 225 257))))))))))))))))))))))))))))))))) (allB_succ' 34 224 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 224 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 224
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 224 257 (accept_3_2 31 224
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 224 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 224 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 224 257 (accept_3_2 28 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 224 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 224 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  26 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 224 257 (accept_3_2 25
  224 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 224 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 224 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 23 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 224 257 (accept_3_2 22 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 224 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 224 257 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 224 257 (accept_3_2 19
  224 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 224 257
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 224 257 (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 257 (accept_3_2 16 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 224 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  14 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 224 257 (accept_3_2 13
  224 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 224 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 224 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 257 (accept_3_2 10 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 224 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 257 (Polychromatic418967fa.accept_21_8_14_5_1_8177
  8 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 224 257 (accept_3_2 7
  224 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 224 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 224 257 (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 257 (accept_3_2 4 224 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 224 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 224 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  224 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 224 257 (accept_3_2 1 224
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224 257)))))))))))))))))))))))))))))))))) (allB_succ' 35 223
  257 (Eq.refl Bool.true) (allA_of_3_0 35 223 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 222 257
  (Eq.refl Bool.true) (allA_succ_of_accept 35 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 257 (accept_3_2 34 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 222 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 222
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 222 257
  (Polychromatic418967fa.accept_20_12_2_17_1_1620 32 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 222 257 (accept_3_2 31 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 222 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 222 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 222 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 222 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 222 257 (accept_3_2 28 222 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 222 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 222 257 (accept_3_2 25 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 222 257 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 257 (accept_3_2 22 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 222 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 222 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 257 (accept_3_2 19 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 222 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 18 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 222 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 257 (accept_3_2 16 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 222 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 222 257 (accept_3_2 13 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 222 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 222 257 (accept_3_2 10 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 222 257 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 222 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 222 257 (accept_3_2 7 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  222 257 (Polychromatic418967fa.accept_11_6_2_4_1_1703 6 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 222 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 257 (accept_3_2 4 222 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 222 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 222 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 222 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 257 (accept_3_2 1 222 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222
  257)))))))))))))))))))))))))))))))))))) (allB_succ' 37 221 257 (Eq.refl Bool.true) (allA_succ_of_accept 36 221 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 221 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 221 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 257 (accept_3_2 34 221 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 221 257 (Polychromatic418967fa.accept_19_14_12_10_1_3368 33 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 257
  (Polychromatic418967fa.accept_28_4_25_5_1_15703 32 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 221 257 (accept_3_2 31 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 221 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 221 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 221 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 257 (accept_3_2 28 221 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 257 (Polychromatic418967fa.accept_7_6_4_5_1_314
  27 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 257
  (Polychromatic418967fa.accept_10_6_1_7_1_342 26 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 257 (accept_3_2 25 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 221 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 257 (accept_3_2 22 221 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 257 (Polychromatic418967fa.accept_15_6_11_2_1_2801 21 221 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 257 (accept_3_2 19 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 257 (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 257 (Polychromatic418967fa.accept_19_17_12_10_1_7404 17 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 257 (accept_3_2 16 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 221 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 257
  (Polychromatic418967fa.accept_10_4_1_7_1_371 14 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 257 (accept_3_2 13 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 257 (Polychromatic418967fa.accept_19_11_12_10_1_7480 11 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 257 (accept_3_2 10 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 221 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 257 (accept_3_2 7 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 257 (accept_3_2 4 221 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 257 (Polychromatic418967fa.accept_16_3_13_1_1_1206 3 221
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 257 (accept_3_2 1 221 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  257))))))))))))))))))))))))))))))))))))) (allB_succ' 38 220 257 (Eq.refl Bool.true) (allA_of_3_0 38 220 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 219 257 (Eq.refl Bool.true) (allA_succ_of_accept 38 219 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 219 257 (accept_3_2 37 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 219 257 (Polychromatic418967fa.accept_20_16_19_17_1_723 36 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 219 257 (accept_3_2 34 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 257 (accept_3_2 31 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 219 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 219 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 257 (accept_3_2 28 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 219 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 219 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 257 (accept_3_2 25 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 219 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 219 257 (Polychromatic418967fa.accept_15_8_9_2_1_1897 23 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 257 (accept_3_2 22 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 219 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 219
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 219 257 (accept_3_2 19 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 219 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 219 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 219 257 (accept_3_2 16 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 219 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 219 257 (accept_3_2 13 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 219 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 257 (accept_3_2 10 219 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 257 (accept_3_2 7 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  219 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 219 257 (Polychromatic418967fa.accept_11_5_10_4_1_1157 5 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 257 (accept_3_2 4 219 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 219 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 257 (accept_3_2 1 219 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  257))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 218 257 (Eq.refl Bool.true) (allA_succ_of_accept 39 218 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 218 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 218 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 218 257 (accept_3_2 37 218 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 218 257 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 218 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 218 257 (accept_3_2 34 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 218 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 218 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 218 257 (accept_3_2 31 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 218 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 218 257
  (Polychromatic418967fa.accept_10_9_8_7_1_714 29 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 218 257 (accept_3_2 28 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 218 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 218 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 218 257 (accept_3_2 25 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 218 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 218 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 218 257 (accept_3_2 22 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 218 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 218 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 257 (accept_3_2 19 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 218 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 257 (accept_3_2 16 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 257 (Polychromatic418967fa.accept_21_14_8_5_1_6586 14 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 257 (accept_3_2 13 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 218 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 218 257 (accept_3_2 10 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  218 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 218 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 257 (accept_3_2 7 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 218 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 257
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 257 (accept_3_2 4 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 2 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 257 (accept_3_2 1 218 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 218 257)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 217 257 (Eq.refl
  Bool.true) (allA_of_3_0 41 217 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 216 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 41 216 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 41 216 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 257 (accept_3_2 40 216 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 216 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 216 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 216 257
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 38 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 216 257 (accept_3_2 37 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 216 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 216 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 216 257 (Polychromatic418967fa.accept_19_16_7_10_1_7456 35 216
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 216 257 (accept_3_2 34 216
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 216 257
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 216 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 216 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 216 257 (accept_3_2 31 216 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 216 257 (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 216 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 216 257 (accept_3_2 28 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 216 257 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 216 257 (Polychromatic418967fa.accept_15_11_6_2_1_1106 26 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 257 (accept_3_2 25 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 216 257 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 216
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 216 257
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 23 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 216 257 (accept_3_2 22 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 216 257 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 216 257 (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 257 (accept_3_2 19 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 216 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 216 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 216 257
  (Polychromatic418967fa.accept_13_4_8_10_1_671 17 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 216 257 (accept_3_2 16 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 216 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 216 257 (Polychromatic418967fa.accept_11_3_7_4_1_1133 14 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 216 257 (accept_3_2 13 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 216 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 216
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 216 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 257 (accept_3_2 10 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  216 257 (Polychromatic418967fa.accept_16_9_8_1_1_1228 9 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 216 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 216 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 257 (accept_3_2 7 216 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 216 257 (Polychromatic418967fa.accept_17_6_12_2_1_10966 6 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 257
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 5 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 216 257 (accept_3_2 4 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  216 257 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 216 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 216 257 (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 257 (accept_3_2 1 216 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 257)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 215 257
  (Eq.refl Bool.true) (allA_succ_of_accept 42 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 257
  (Polychromatic418967fa.accept_15_11_5_2_1_520 41 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 257 (accept_3_2 40 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 257 (accept_3_2 37 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 257 (Polychromatic418967fa.accept_23_13_8_4_1_12532 36 215 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 257
  (Polychromatic418967fa.accept_11_2_6_4_1_3028 35 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 257 (accept_3_2 34 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 257 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 257 (accept_3_2 31 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 215 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 257 (accept_3_2 28 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 257 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 257 (accept_3_2 25 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 257
  (Polychromatic418967fa.accept_10_3_5_7_1_330 23 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 215 257 (accept_3_2 22 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 215 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 215 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 257 (accept_3_2 19 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 257
  (Polychromatic418967fa.accept_13_4_7_10_1_1200 17 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 257 (accept_3_2 16 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 257 (accept_3_2 13 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 257
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 257 (accept_3_2 10 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 257 (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 257 (Polychromatic418967fa.accept_10_8_5_7_1_358 8 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 257 (accept_3_2 7 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 257
  (Polychromatic418967fa.accept_20_5_15_17_1_7077 5 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 257 (accept_3_2 4 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 215 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 257 (accept_3_2 1 215 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 257))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 214 257 (Eq.refl
  Bool.true) (allA_of_3_0 44 214 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 213 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 213 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 257 (accept_3_2 43 213 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 213 257 (Polychromatic418967fa.accept_15_12_3_2_1_2756 42 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 257
  (Polychromatic418967fa.accept_13_2_5_10_1_250 41 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 257 (accept_3_2 40 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 213 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 257 (accept_3_2 37 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 257 (accept_3_2 34 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 213 257 (Polychromatic418967fa.accept_19_14_4_10_1_3344 33 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 257 (accept_3_2 31 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 257 (accept_3_2 28 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 213 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 257 (accept_3_2 25 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 213 257
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 257 (accept_3_2 22 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 213 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 257 (accept_3_2 19 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 257 (Polychromatic418967fa.accept_21_18_3_5_1_9796 18 213 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 213 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 213 257 (accept_3_2 16 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 213 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 257 (accept_3_2 13 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 257 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 213 257
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 257 (accept_3_2 10 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  213 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 257 (accept_3_2 7 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 213 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 257
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 257 (accept_3_2 4 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 213 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 257 (accept_3_2 1 213 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 257))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 212 257 (Eq.refl
  Bool.true) (allA_succ_of_accept 45 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 212 257 (Polychromatic418967fa.accept_10_4_2_7_1_373
  44 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 212 257 (accept_3_2 43
  212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 212 257
  (Polychromatic418967fa.accept_20_2_12_17_1_5547 42 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 212 257 (Polychromatic418967fa.accept_21_20_2_5_1_15684 41 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 212 257 (accept_3_2 40 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 212 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 212 257
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 212 257 (accept_3_2 37 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 212 257 (Polychromatic418967fa.accept_24_12_20_17_1_13891 36 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 257 (Polychromatic418967fa.accept_10_5_2_7_1_345 35 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 212 257 (accept_3_2 34 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 212 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 212 257
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 212 257 (accept_3_2 31 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 212 257 (Polychromatic418967fa.accept_16_14_4_1_1_3049 30 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 212 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 29 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 212 257 (accept_3_2 28 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 212 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 26 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 212 257 (accept_3_2 25 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 212 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 212 257 (Polychromatic418967fa.accept_22_1_14_15_1_12583 23 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 212 257 (accept_3_2 22 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 212 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 212 257
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 212 257 (accept_3_2 19 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 212 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 212 257 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 212 257 (accept_3_2 16 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 212 257
  (Polychromatic418967fa.accept_10_4_2_7_1_373 14 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 212 257 (accept_3_2 13 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 212 257 (Polychromatic418967fa.accept_16_12_4_1_1_1257 12 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 212 257 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 212 257 (accept_3_2 10 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 212 257
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 212 257 (accept_3_2 7 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  212 257 (Polychromatic418967fa.accept_13_6_4_10_1_660 6 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 212 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 5 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 257 (accept_3_2 4 212 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 257 (accept_3_2 1 212 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  257)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 211 257 (Eq.refl Bool.true) (allA_of_3_0 47 211 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 210 257 (Eq.refl Bool.true) (allA_succ_of_accept 47 210 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 210 257 (accept_3_2 46 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 210 257 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 210 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 44 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 257 (accept_3_2 43 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 210 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 210 257
  (Polychromatic418967fa.accept_11_8_1_4_1_2318 41 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 210 257 (accept_3_2 40 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 210 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 210 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 257 (accept_3_2 37 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 210 257 (Polychromatic418967fa.accept_19_17_1_10_1_4671 36 210 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 210 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 210 257 (accept_3_2 34 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 210 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 210 257 (Polychromatic418967fa.accept_13_6_2_10_1_1240 32 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 257 (accept_3_2 31 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 210 257 (Polychromatic418967fa.accept_11_8_1_4_1_2318 30 210
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 210 257
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 210 257 (accept_3_2 28 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 210 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 210 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 257 (accept_3_2 25 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 210 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 210 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 210 257 (accept_3_2 22 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 210 257 (Polychromatic418967fa.accept_13_8_2_10_1_652 21 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 210 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 257 (accept_3_2 19 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 210 257 (Polychromatic418967fa.accept_13_5_2_10_1_248 18 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 210 257
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 210 257 (accept_3_2 16 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 210 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 210 257 (Polychromatic418967fa.accept_19_14_1_10_1_11713 14 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 210 257 (accept_3_2 13 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 257 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 210
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 210 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 210 257 (accept_3_2 10 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  210 257 (Polychromatic418967fa.accept_16_9_2_1_1_3077 9 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 210 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 257 (accept_3_2 7 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 210 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 257
  (Polychromatic418967fa.accept_13_5_2_10_1_248 5 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 210 257 (accept_3_2 4 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  210 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 210 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 257 (accept_3_2 1 210 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 210 257)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 209 257 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 209 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 257
  (Polychromatic418967fa.accept_20_7_9_17_1_8558 47 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 257 (accept_3_2 46 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 257 (Polychromatic418967fa.accept_22_1_11_15_1_6075 45 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 257 (accept_3_2 43 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 257
  (Polychromatic418967fa.accept_23_18_2_4_1_9121 41 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 257 (accept_3_2 40 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 257 (Polychromatic418967fa.accept_10_8_9_7_1_1118 38 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 257 (accept_3_2 37 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 209 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 257 (accept_3_2 34 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 257 (accept_3_2 31 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 257
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 257 (accept_3_2 28 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 257 (Polychromatic418967fa.accept_15_12_14_2_1_3794 27 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 257 (accept_3_2 25 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 257
  (Polychromatic418967fa.accept_21_2_20_5_1_6599 23 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 257 (accept_3_2 22 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 257 (Polychromatic418967fa.accept_14_6_13_5_1_534 20 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 257 (accept_3_2 19 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 257 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 209 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 257 (accept_3_2 16 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 257 (Polychromatic418967fa.accept_17_14_5_2_1_4559 14 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 257 (accept_3_2 13 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 209 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 257
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 257 (accept_3_2 10 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 257 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 257 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 257 (accept_3_2 7 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 209 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 257
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 5 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 257 (accept_3_2 4 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 209 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 257 (Polychromatic418967fa.accept_10_2_9_7_1_720 2 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 257 (accept_3_2 1 209 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 257))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 208 257
  (Eq.refl Bool.true) (allA_of_3_0 50 208 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 207 257 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 257 (accept_3_2 49 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 207 257
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 207 257 (accept_3_2 46 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 207 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 207 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 207 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 257 (accept_3_2 43 207 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 207 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 207 257 (accept_3_2 40 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 207 257 (Polychromatic418967fa.accept_17_5_3_2_1_5847 39 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 257 (accept_3_2 37 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 207 257
  (Polychromatic418967fa.accept_11_2_9_4_1_310 35 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 257 (accept_3_2 34 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 207 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 207 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 257 (accept_3_2 31 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 207 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 207 257 (accept_3_2 28 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 207 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 257 (accept_3_2 25 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 257 (Polychromatic418967fa.accept_11_2_9_4_1_310 24 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 207 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 257 (accept_3_2 22 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 207 257 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 207 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 257 (accept_3_2 19 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 207 257
  (Polychromatic418967fa.accept_31_17_21_9_1_15702 17 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 207 257 (accept_3_2 16 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 207 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 207 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 257 (accept_3_2 13 207 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 257
  (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 257 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 257 (accept_3_2 10 207 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 257 (accept_3_2 7 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 257 (Polychromatic418967fa.accept_15_5_12_2_1_2820 5 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 257 (accept_3_2 4 207 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 257 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 207 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 257 (accept_3_2 1 207 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  257))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 206 257 (Eq.refl Bool.true) (allA_succ_of_accept
  51 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 206 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 206 257 (accept_3_2 49 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 206 257 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 206 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 206 257 (accept_3_2 46 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 206 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 206 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 206 257 (accept_3_2 43 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 206 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 206 257
  (Polychromatic418967fa.accept_10_1_6_7_1_710 41 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 206 257 (accept_3_2 40 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 206 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 206 257 (accept_3_2 37 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 206 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 206 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 206 257 (accept_3_2 34 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 206 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 206 257 (Polychromatic418967fa.accept_12_8_2_5_1_844 32 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 206 257 (accept_3_2 31 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 206 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 206 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 206 257
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 206 257 (accept_3_2 28 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 206 257 (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 206 257 (accept_3_2 25 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 206 257 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 206 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 206 257
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 206 257 (accept_3_2 22 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 206 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 206 257 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 206 257 (accept_3_2 19 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 206 257 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 206 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 206 257
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 206 257 (accept_3_2 16 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 257 (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 206
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 257 (accept_3_2 13 206
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 206 257
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 257 (accept_3_2 10 206 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 206 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 257 (Polychromatic418967fa.accept_7_1_3_5_1_33 8
  206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 257 (accept_3_2 7 206
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 206 257
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 206 257 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 206 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 257 (accept_3_2 4 206 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 206 257 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 257 (Polychromatic418967fa.accept_7_2_3_5_1_34 2
  206 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 206 257 (accept_3_2 1 206
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206 257))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 205 257 (Eq.refl Bool.true) (allA_of_3_0 53 205 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 54 204 257 (Eq.refl Bool.true) (allA_succ_of_accept 53 204 257 (Polychromatic418967fa.accept_7_4_1_5_1_540
  53 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 257 (accept_3_2 52
  204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 204 257
  (Polychromatic418967fa.accept_10_1_4_7_1_374 51 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 204 257 (Polychromatic418967fa.accept_16_2_12_1_1_3086 50 204 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 257 (accept_3_2 49 204 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 204 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 204 257 (Polychromatic418967fa.accept_9_2_6_5_1_227
  47 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 257 (accept_3_2 46
  204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 204 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 45 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 204 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 204 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 257 (accept_3_2 43 204 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 204 257 (Polychromatic418967fa.accept_10_2_4_7_1_352 42 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 204 257
  (Polychromatic418967fa.accept_7_6_1_5_1_322 41 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 204 257 (accept_3_2 40 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 204 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 204 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 204 257 (accept_3_2 37 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 204 257 (Polychromatic418967fa.accept_16_4_12_1_1_1204 36 204 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 204 257
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 204 257 (accept_3_2 34 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 204 257 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 204 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 32 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 257 (accept_3_2 31 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 204 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 204 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 29 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 204 257 (accept_3_2 28 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 204 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 204 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 257 (accept_3_2 25 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 204 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 204 257
  (Polychromatic418967fa.accept_10_3_4_7_1_353 23 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 257 (accept_3_2 22 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 204 257 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 204 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 204 257 (accept_3_2 19 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 257 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 204 257
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 204 257 (accept_3_2 16 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 204 257 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 204 257 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 257 (accept_3_2 13 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 257 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 204 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 257
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 257 (accept_3_2 10 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  204 257 (Polychromatic418967fa.accept_21_9_15_5_1_3500 9 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 204 257 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 257 (accept_3_2 7 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 257 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 204 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 257
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 257 (accept_3_2 4 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  204 257 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 204 257 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 257 (accept_3_2 1 204 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 257)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 203 257
  (Eq.refl Bool.true) (allA_succ_of_accept 54 203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 257
  (Polychromatic418967fa.accept_21_11_14_5_1_6596 53 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 203 257 (accept_3_2 52 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 203 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 203 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 257 (accept_3_2 49
  203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 257
  (Polychromatic418967fa.accept_17_14_16_2_1_4553 48 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 257 (Polychromatic418967fa.accept_16_15_11_1_1_7767 47 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 257 (accept_3_2 46 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 203
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 257
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 44 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 257 (accept_3_2 43 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 257 (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 257 (accept_3_2 40 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 257 (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 203
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 257 (accept_3_2 37 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 257 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 35 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 257 (accept_3_2 34 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 257 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 203
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 257
  (Polychromatic418967fa.accept_11_10_5_4_1_711 32 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 257 (accept_3_2 31 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 257 (Polychromatic418967fa.accept_21_8_14_5_1_8177 29 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 257 (accept_3_2 28 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 257 (Polychromatic418967fa.accept_24_3_11_17_1_10650 27
  203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 257 (accept_3_2 25 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 257 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 257 (accept_3_2 22 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 257 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 203
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 257
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 20 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 257 (accept_3_2 19 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 257 (Polychromatic418967fa.accept_13_4_8_10_1_671 17 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 257 (accept_3_2 16 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 203
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 257 (accept_3_2 13 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 257 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 257 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 257 (accept_3_2 10 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 257 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 203 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 257
  (Polychromatic418967fa.accept_17_8_16_2_1_10847 8 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 257 (accept_3_2 7 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 257 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 257 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 203 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 257 (accept_3_2 4 203 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 257 (Polychromatic418967fa.accept_19_3_13_10_1_7461 3 203 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 257
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 257 (accept_3_2 1 203 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 202 257 (Eq.refl Bool.true) (allA_of_3_0 56
  202 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 201 257 (Eq.refl Bool.true) (allA_succ_of_accept 56
  201 257 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 201 257 (accept_3_2 55 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 201 257 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 201 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 201 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 257 (accept_3_2 52 201 257
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240
  51 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 257 (accept_3_2 49 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 201 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 48 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 201 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 257 (accept_3_2 46 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 257 (Polychromatic418967fa.accept_16_13_9_1_1_3022 45 201 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 257 (accept_3_2 43 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 201 257 (Polychromatic418967fa.accept_13_2_6_10_1_2703 41 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 257 (accept_3_2 40 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 201
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 201 257 (accept_3_2 37 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 201 257 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 201 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 257 (accept_3_2 34 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 201 257 (accept_3_2 31 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 201 257 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 201 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 257 (accept_3_2 28 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 257 (accept_3_2 25 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 201 257 (Polychromatic418967fa.accept_15_8_6_2_1_1128 23 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 257 (accept_3_2 22 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 257 (Polychromatic418967fa.accept_16_5_9_1_1_2070 21 201
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 257 (accept_3_2 19 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 257 (Polychromatic418967fa.accept_11_7_3_4_1_729 18 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 257 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 257 (accept_3_2 16 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 257 (accept_3_2 13 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 257 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 257 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 257 (accept_3_2 10 201 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 257 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 257 (accept_3_2 7 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 257 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 257 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 257 (accept_3_2 4 201 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 257 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 201 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 257
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 257 (accept_3_2 1 201 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 200 257 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 200 257 (Polychromatic418967fa.accept_13_4_5_10_1_1247 56 200
  257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 200 257 (accept_3_2 55 200
  257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 200 257
  (Polychromatic418967fa.accept_13_2_5_10_1_250 54 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 200 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 200 257 (accept_3_2 52 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 200 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 50
  200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 200 257 (accept_3_2 49
  200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 200 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 48 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 200 257 (Polychromatic418967fa.accept_13_8_5_10_1_2701 47 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 200 257 (accept_3_2 46 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 200 257 (Polychromatic418967fa.accept_7_2_4_5_1_313
  44 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 200 257 (accept_3_2 43
  200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 200 257
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 200 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 200 257 (accept_3_2 40 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 200 257 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 200 257 (accept_3_2 37
  200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 200 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 36 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 200 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 200 257 (accept_3_2 34 200 257 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 200 257
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 32 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 200 257 (accept_3_2 31 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 200 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 200 257 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 200 257 (accept_3_2 28 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 200 257
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 200 257 (accept_3_2 25 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 200 257 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 200 257 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 200 257 (accept_3_2 22 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 200 257
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 200 257 (accept_3_2 19 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 200 257 (Polychromatic418967fa.accept_15_3_5_2_1_2816 18 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 200 257 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 200 257 (accept_3_2 16 200 257 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 257
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 257 (accept_3_2 13 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 257 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 257 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 200 257 (accept_3_2 10 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 257
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 200 257 (accept_3_2 7 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 257 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 257 (Polychromatic418967fa.accept_26_5_18_23_1_15701 5 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 257 (accept_3_2 4 200 257 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 257 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 257
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 257
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 257 (accept_3_2 1 200 257 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  257))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_257_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))


