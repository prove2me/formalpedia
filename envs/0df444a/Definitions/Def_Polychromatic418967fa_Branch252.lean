-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch252
-- name    : Polychromatic418967fa_Branch252
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:26.001409+00:00
-- url     : https://prove2.me/theorems/db33fc35-43c2-4b26-bd84-17f13d3f5b58
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch252_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_252 : allB 252 252 :=
  allB_succ' 2 251 252 (Eq.refl Bool.true) (allA_succ_of_accept 1 251 252 (accept_3_4 1 251 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 251 252)) (allB_succ' 3 250 252 (Eq.refl Bool.true) (allA_succ_of_gcd 2 250 252 2 1 125
  126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 252
  (Polychromatic418967fa.accept_13_1_3_5_1_140 1 250 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 252))) (allB_succ' 4 249 252 (Eq.refl Bool.true) (allA_succ_of_gcd 3 249 252 3 1 83 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 249 252
  (Polychromatic418967fa.accept_16_2_9_12_1_46 2 249 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 249 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 249 252)))) (allB_succ' 5 248 252 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  248 252 4 1 62 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 248 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 248 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 248 252 2 1 124 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 248 252 (accept_3_4 1 248 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 248 252))))) (allB_succ' 6 247 252 (Eq.refl Bool.true) (allA_succ_of_accept 5 247 252 (accept_3_5 5 247 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4
  247 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 247 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 252 (accept_3_5 2 247 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 252 (Polychromatic418967fa.accept_22_1_5_10_1_10706 1 247 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 252)))))) (allB_succ' 7 246 252 (Eq.refl Bool.true) (allA_succ_of_gcd 6 246 252 6 1 41 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 246 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 246 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 246 252 2 2 123 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 246 252 3 1 82 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 246 252 2 1 123 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 246 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 246 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 246 252))))))) (allB_succ' 8 245 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 245 252 7 1 35 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 6 245 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 6 245 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 252 (Polychromatic418967fa.accept_25_5_20_2_1_15347 5 245
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 252 (accept_3_4 4 245 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 245 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3
  245 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 252
  (Polychromatic418967fa.accept_15_2_5_12_1_369 2 245 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 245 252 (accept_3_4 1 245 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245
  252)))))))) (allB_succ' 9 244 252 (Eq.refl Bool.true) (allA_succ_of_gcd 8 244 252 4 2 61 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 244 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 244 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 244 252 2 3 122 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 244 252 (accept_3_5 5 244 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 244 252 4 1 61 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 244 252 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 244 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 252 2 1 122 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426
  1 244 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 252))))))))) (allB_succ' 10 243
  252 (Eq.refl Bool.true) (allA_succ_of_gcd 9 243 252 9 1 27 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 243 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 243 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 243 252 3 2 81 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 243 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 243 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 243 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 252 3 1 81 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 2 243 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 243 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 252)))))))))) (allB_succ' 11 242 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 242 252 2 5 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 242 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 242 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 242 252 2 4 121 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 242 252 (accept_3_4 7 242 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 242 252 2 3 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 242 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543
  5 242 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 252 2 2 121 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 252
  (Polychromatic418967fa.accept_13_3_8_5_1_974 3 242 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 252 2 1 121 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 252 (accept_3_4 1 242 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  252))))))))))) (allB_succ' 12 241 252 (Eq.refl Bool.true) (allA_succ_of_accept 11 241 252 (accept_3_5 11 241 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 241 252
  (Polychromatic418967fa.accept_19_10_13_5_1_3091 10 241 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 241 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 252 (accept_3_5 8 241 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 252 (Polychromatic418967fa.accept_19_7_13_5_1_7125 7 241 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 6 241 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 252 (accept_3_5 5 241 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 241 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 241 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 252 (accept_3_5 2 241 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 252 (Polychromatic418967fa.accept_27_1_25_9_1_15406 1 241 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 252)))))))))))) (allB_succ' 13 240 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 240 252 12 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 240 252 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 240 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 252 2 5 120 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 240 252 3 3 80 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 240 252 4 2 60 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 252
  (Polychromatic418967fa.accept_19_7_12_5_1_7123 7 240 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 252 6 1 40 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 240 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 5 240 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 240 252 4 1 60 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 240 252 3 1 80 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 240 252 2 1 120 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1
  240 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 252))))))))))))) (allB_succ' 14 239
  252 (Eq.refl Bool.true) (allA_succ_of_accept 13 239 252 (accept_3_4 13 239 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 239 252 (Polychromatic418967fa.accept_19_12_11_5_1_950 12 239 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 239 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 239 252 (accept_3_4 10 239 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  239 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 239 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 239 252 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 239 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 252 (accept_3_4 7 239 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 252 (Polychromatic418967fa.accept_19_6_11_5_1_5628 6 239
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 252
  (Polychromatic418967fa.accept_22_5_19_10_1_15391 5 239 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 239 252 (accept_3_4 4 239 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 239 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 239 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 239 252 (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 239
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 252 (accept_3_4 1 239 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 239 252)))))))))))))) (allB_succ' 15 238 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 238 252 14 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 238 252 (Polychromatic418967fa.accept_19_13_10_5_1_11329 13 238 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 238 252 2 6 119 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 238 252 (accept_3_5 11 238 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 238 252 2 5 119 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 238 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 238 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 238 252 2 4 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 238 252 7 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 238 252 2 3 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 238 252 (accept_3_5 5 238 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 252 2 2 119 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 238 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 252 2 1 119 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 1 238 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 252))))))))))))))) (allB_succ' 16 237 252 (Eq.refl Bool.true) (allA_succ_of_gcd 15 237 252 3 5 79 84
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 237 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 237 252 (Polychromatic418967fa.accept_19_13_9_5_1_8541 13 237 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 237 252 3 4 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 237 252 (Polychromatic418967fa.accept_13_11_3_5_1_982
  11 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 252
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 10 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 237 252 3 3 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 237 252 (Polychromatic418967fa.accept_13_8_3_5_1_1636 8 237 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 252 (Polychromatic418967fa.accept_19_7_9_5_1_8590
  7 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 252 3 2 79 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 237 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 237 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 237 252 3 1 79 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 2 237 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 237 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 237 252)))))))))))))))) (allB_succ' 17 236 252 (Eq.refl Bool.true) (allA_succ_of_gcd 16 236 252 4 4 59 63
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 15 236 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 236 252 2 7 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 236 252 (accept_3_4 13 236 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 236 252 4 3 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 236 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 236 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 252 2 5 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9
  236 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 236 252 4 2 59 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 236 252 (accept_3_4 7
  236 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 236 252 2 3 118 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 236 252
  (Polychromatic418967fa.accept_22_5_16_10_1_7349 5 236 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 236 252 4 1 59 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 236 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 3 236 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 236 252 2 1 118 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 236 252 (accept_3_4 1 236 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 252))))))))))))))))) (allB_succ' 18 235 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 235 252 (accept_3_5 17 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 235 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 16 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 235 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 235 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 252 (accept_3_5 14 235 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 235 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 252 (accept_3_5 11 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 10 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 235 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 252 (accept_3_5 8 235 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 235 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 252 (accept_3_5 5 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 4 235 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 235 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 252 (accept_3_5 2 235 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 252 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 235 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 252)))))))))))))))))) (allB_succ' 19 234 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 234 252 18 1 13 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 234 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 234 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 252 2 8 117 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 234 252 3 5 78 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 234 252 2 7 117 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 234 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 234 252 6 2 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 234 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 11 234 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 252 2 5 117 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 234 252 9 1 26 28 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 252 2 4 117 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 234 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 252 6 1 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 234 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 252 2 2 117 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 252 3 1 78 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 252 2 1 117 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 252
  (Polychromatic418967fa.accept_17_1_13_14_1_478 1 234 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 252))))))))))))))))))) (allB_succ' 20 233 252 (Eq.refl Bool.true) (allA_succ_of_accept 19 233 252
  (accept_3_4 19 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 252
  (Polychromatic418967fa.accept_15_3_8_12_1_900 18 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 233 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 233 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 252 (accept_3_4 16 233 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 233 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 233 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 14 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 233 252 (accept_3_4 13 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 233 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 233 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 233 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 252 (accept_3_4 10 233 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 233 252 (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 233
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 252
  (Polychromatic418967fa.accept_13_8_12_5_1_1604 8 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 233 252 (accept_3_4 7 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  233 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 6 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 233 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 233 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 252 (accept_3_4 4 233 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 233 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 233 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 233 252 (accept_3_4 1 233 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233
  252)))))))))))))))))))) (allB_succ' 21 232 252 (Eq.refl Bool.true) (allA_succ_of_gcd 20 232 252 4 5 58 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 232 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 19 232 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 232 252 2 9 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 232 252 (accept_3_5 17 232 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 232 252 4 4 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 232 252 (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 232 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 252 2 7 116 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 252
  (Polychromatic418967fa.accept_11_2_1_10_1_196 13 232 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 252 4 3 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 232 252 (accept_3_5 11 232 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  232 252 2 5 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 232 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 232 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 252 4 2 58 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 7 232 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 232 252 2 3 116 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 232 252 (accept_3_5 5
  232 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 232 252 4 1 58 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 232 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 232 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 232 252 2 1 116 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 232 252 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 232 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 252))))))))))))))))))))) (allB_succ' 22 231 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 231 252 21 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 231 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 231 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 231 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 231 252 3 6 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 231 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 231 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 231
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 231 252 3 5 77 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 231 252 7 2 33 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 231 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 231 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 231 252 3 4 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 231 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 231 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 252 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 231
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 252 3 3 77 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 8 231 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 231 252 7 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 231 252 3 2 77 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 231 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 231 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 231
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 252 3 1 77 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 252
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 2 231 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 231 252 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 231 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 231 252)))))))))))))))))))))) (allB_succ' 23 230 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 230 252 2 11 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 230 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 230 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 230 252 2 10 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 230 252 (accept_3_4 19 230 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 230 252 2 9 115 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 230 252
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 230 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 230 252 2 8 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 230 252 (Polychromatic418967fa.accept_13_2_9_5_1_959 15 230 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 230 252 2 7 115 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 230 252 (accept_3_4 13 230 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 230 252 2 6 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 230 252
  (Polychromatic418967fa.accept_27_11_14_9_1_5575 11 230 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 230 252 2 5 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 230 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 230 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 230 252 2 4 115 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 230 252 (accept_3_4 7 230 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 230 252 2 3 115 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 230 252
  (Polychromatic418967fa.accept_17_5_9_14_1_4282 5 230 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 230 252 2 2 115 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 230 252 (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 230 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 230 252 2 1 115 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 230 252 (accept_3_4 1 230 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 230 252))))))))))))))))))))))) (allB_succ' 24 229 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 229 252 (accept_3_5 23 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 229 252 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 229 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 252 (accept_3_5 20 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 229 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 19 229 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 252
  (Polychromatic418967fa.accept_19_18_1_5_1_5720 18 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 229 252 (accept_3_5 17 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 229 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 16 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 252 (Polychromatic418967fa.accept_19_15_1_5_1_3013 15 229 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 252 (accept_3_5 14 229 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 252 (Polychromatic418967fa.accept_22_13_9_10_1_15235 13
  229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 12 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 252 (accept_3_5 11 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 10 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 252 (accept_3_5 8 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 229 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 252
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 6 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 252 (accept_3_5 5 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 229 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 3 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 252 (accept_3_5 2 229 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 229 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 252)))))))))))))))))))))))) (allB_succ' 25 228 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 228 252 12 2 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 228
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 252 2 11 114 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 228 252 3 7 76 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 228 252 4 5 57 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 252
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 19 228 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 252 6 3 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 17 228 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 252 4 4 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 252 3 5 76 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 252 2 7 114 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 228 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 228 252 12 1 19 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 228 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 228 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 252 2 5 114 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 228 252 3 3 76 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 252 4 2 57 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 252
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 228 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 252 6 1 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 228 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 252 4 1 57 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 252 3 1 76 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 252 2 1 114 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 252 (Polychromatic418967fa.accept_16_1_4_12_1_376 1
  228 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 252)))))))))))))))))))))))))
  (allB_succ' 26 227 252 (Eq.refl Bool.true) (allA_succ_of_accept 25 227 252 (accept_3_4 25 227 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 252 (accept_3_4 22 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 252 (accept_3_4 19 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 227
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 252
  (Polychromatic418967fa.accept_13_4_6_5_1_2333 17 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 227 252 (accept_3_4 16 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 227 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 227 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 252 (accept_3_4 13 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 252 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 227
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 252
  (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 252 (accept_3_4 10 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 252 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 252 (accept_3_4 7 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 6 227 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 252
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 252 (accept_3_4 4 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 227 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 252 (Polychromatic418967fa.accept_19_2_18_5_1_11293 2 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 252 (accept_3_4 1 227 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 227 252)))))))))))))))))))))))))) (allB_succ' 27 226 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 226 252 2 13 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 226 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 25 226 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 226 252 2 12 113 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 226 252 (accept_3_5 23 226 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 226 252 2 11 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 226 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 226 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 226 252 2 10 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 226 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 19 226 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 226 252 2 9 113 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 226 252 (accept_3_5 17 226 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 226 252 2 8 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 226 252
  (Polychromatic418967fa.accept_16_15_2_12_1_1799 15 226 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 226 252 2 7 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 226 252 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 226 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 226 252 2 6 113 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 226 252 (accept_3_5 11
  226 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 226 252 2 5 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 226 252
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 226 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 226 252 2 4 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 226 252 (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 226 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 226 252 2 3 113 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 226 252 (accept_3_5 5 226 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 226 252 2 2 113 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 226 252 (Polychromatic418967fa.accept_19_3_17_5_1_955 3
  226 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 252 2 1 113 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 1 226 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 252))))))))))))))))))))))))))) (allB_succ' 28 225 252 (Eq.refl Bool.true) (allA_succ_of_gcd 27 225 252 9
  3 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 225
  252 (Polychromatic418967fa.accept_11_4_5_10_1_926 26 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 225 252 (Polychromatic418967fa.accept_13_12_4_5_1_1637 25 225 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 225 252 3 8 75 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 225 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 22 225 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 225 252 3 7 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 225 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792
  20 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 252
  (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 225 252 9 2 25 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 225 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 225 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 252 (Polychromatic418967fa.accept_22_16_5_10_1_10671 16
  225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 252 3 5 75 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 252
  (Polychromatic418967fa.accept_13_1_4_5_1_113 14 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 225 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 252 3 4 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 252
  (Polychromatic418967fa.accept_16_11_1_12_1_1795 11 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 225 252 (Polychromatic418967fa.accept_13_10_4_5_1_2331 10 225 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 225 252 9 1 25 28 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 225 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 252 3 2 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 225 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 252
  (Polychromatic418967fa.accept_11_4_5_10_1_926 4 225 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 252 3 1 75 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 2 225 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 252 (Polychromatic418967fa.accept_13_1_4_5_1_113 1 225 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 252)))))))))))))))))))))))))))) (allB_succ'
  29 224 252 (Eq.refl Bool.true) (allA_succ_of_gcd 28 224 252 28 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 224 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 224 252 2 13 112 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 224 252 (accept_3_4 25
  224 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 224 252 4 6 56 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 224 252
  (Polychromatic418967fa.accept_17_6_3_14_1_2078 23 224 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 224 252 2 11 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 224 252 7 3 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 224 252 4 5 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 224 252 (accept_3_4 19 224 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 224 252 2 9 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 224 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 224 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 252 4 4 56 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 252
  (Polychromatic418967fa.accept_13_2_3_5_1_2294 15 224 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 252 14 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 252 (accept_3_4 13 224 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 252 4 3 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 224 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 224 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 252 2 5 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 9
  224 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 224 252 4 2 56 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 224 252 7 1 32 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 224 252 2 3 112 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 224 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 224 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 224 252 4 1 56 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 224 252 (Polychromatic418967fa.accept_25_3_24_2_1_15405 3 224 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 224 252 2 1 112 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 224 252 (accept_3_4 1 224 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 224 252))))))))))))))))))))))))))))) (allB_succ' 30 223 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 223 252 (accept_3_5 29 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 223 252 (Polychromatic418967fa.accept_19_9_14_5_1_1890 28 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 223 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 223 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 252 (accept_3_5 26 223 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 223 252 (Polychromatic418967fa.accept_10_5_3_2_1_899 25 223 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 252
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 223 252 (accept_3_5 23 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 223 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 22 223 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 223
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 252 (accept_3_5 20 223
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 223 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 223 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 252 (accept_3_5 17 223 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 223 252 (Polychromatic418967fa.accept_13_3_2_5_1_1632 16 223 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 252 (accept_3_5 14 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 252 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 223 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 252 (accept_3_5 11 223 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 223 252 (Polychromatic418967fa.accept_13_9_2_5_1_2310 9 223 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 252 (accept_3_5 8 223 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 223 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 7 223 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 252
  (Polychromatic418967fa.accept_19_6_14_5_1_4339 6 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 252 (accept_3_5 5 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 252 (Polychromatic418967fa.accept_13_4_2_5_1_4045 4 223 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 223 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 252 (accept_3_5 2 223 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 223 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 252)))))))))))))))))))))))))))))) (allB_succ' 31 222
  252 (Eq.refl Bool.true) (allA_succ_of_gcd 30 222 252 6 5 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 222 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 222 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 252 2 14 111 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 222 252 3 9 74 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 222 252 2 13 111 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 222 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 252 6 4 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 222 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 222 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 252 2 11 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 222 252 3 7 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 222 252 2 10 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 19 222 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 252 6 3 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 222 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 17 222 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 252 2 8 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 222 252 3 5 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 222 252 2 7 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 252
  (Polychromatic418967fa.accept_17_13_1_14_1_1149 13 222 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 222 252 6 2 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 222 252 (Polychromatic418967fa.accept_19_11_13_5_1_5714 11 222 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 252 2 5 111 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 222 252 3 3 74 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 252 2 4 111 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 252
  (Polychromatic418967fa.accept_19_7_13_5_1_7125 7 222 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 252 6 1 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 252 (Polychromatic418967fa.accept_22_5_2_10_1_10683 5 222 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 252 2 2 111 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 222 252 3 1 74 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 252 2 1 111 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 252
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 222 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 252))))))))))))))))))))))))))))))) (allB_succ' 32 221 252 (Eq.refl Bool.true) (allA_succ_of_accept 31
  221 252 (accept_3_4 31 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 221 252
  (Polychromatic418967fa.accept_19_11_12_5_1_7124 30 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 252 (accept_3_4 28 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 252 (Polychromatic418967fa.accept_19_8_12_5_1_7122 27 221
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 252 (accept_3_4 25 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 252 (accept_3_4 22 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 252 (Polychromatic418967fa.accept_23_21_14_22_1_13707 21
  221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 252
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 252 (accept_3_4 19 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 252 (Polychromatic418967fa.accept_23_18_14_22_1_15221 18 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 252 (accept_3_4 16 221 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 252 (Polychromatic418967fa.accept_16_15_13_12_1_1787 15
  221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 252
  (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 221 252 (accept_3_4 13 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 221 252 (Polychromatic418967fa.accept_25_12_21_2_1_15404 12 221 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 252
  (Polychromatic418967fa.accept_19_11_12_5_1_7124 11 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 221 252 (accept_3_4 10 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 221 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 221 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 252 (Polychromatic418967fa.accept_15_8_11_12_1_1626 8 221
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 221 252 (accept_3_4 7 221 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 221 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6
  221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 221 252
  (Polychromatic418967fa.accept_22_5_1_10_1_15198 5 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 221 252 (accept_3_4 4 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  221 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 221 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 221 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 221 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 221 252 (accept_3_4 1 221 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 221 252)))))))))))))))))))))))))))))))) (allB_succ' 33 220 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 220 252 4 8 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 220 252 (Polychromatic418967fa.accept_19_12_11_5_1_950 31 220 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 252 2 15 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 252 (accept_3_5 29 220 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 252 4 7 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601 27 220
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 220 252 2 13 110 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 220 252
  (Polychromatic418967fa.accept_17_8_16_14_1_4261 25 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 220 252 4 6 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 220 252 (accept_3_5 23 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 220 252 2 11 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 220 252 (Polychromatic418967fa.accept_13_8_12_5_1_1604 21 220 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 252 4 5 55 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 252
  (Polychromatic418967fa.accept_13_6_12_5_1_2304 19 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 252 2 9 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 252 (accept_3_5 17 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 252 4 4 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 220 252 (Polychromatic418967fa.accept_13_2_12_5_1_1602 15 220 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 252 2 7 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 252
  (Polychromatic418967fa.accept_15_13_10_12_1_2503 13 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 220 252 4 3 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 220 252 (accept_3_5 11 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 252 2 5 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 252 (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 220 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 252 4 2 55 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 252 2 3 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 220 252 (accept_3_5 5 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 220 252 4 1 55 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 220 252 (Polychromatic418967fa.accept_23_3_13_22_1_15403 3 220 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 252 2 1 110 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 252 (Polychromatic418967fa.accept_13_1_12_5_1_1601
  1 220 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220
  252))))))))))))))))))))))))))))))))) (allB_succ' 34 219 252 (Eq.refl Bool.true) (allA_succ_of_gcd 33 219 252 3 11 73
  84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 219 252
  (Polychromatic418967fa.accept_13_6_11_5_1_133 32 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 219 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 219 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 219 252 3 10 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 219 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348
  29 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 252
  (Polychromatic418967fa.accept_22_6_21_10_1_12180 28 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 219 252 3 9 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 219 252 (Polychromatic418967fa.accept_16_10_11_12_1_4835 26 219 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 252
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 219 252 3 8 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 219 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 219 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 252
  (Polychromatic418967fa.accept_19_3_10_5_1_4314 22 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 219 252 3 7 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 219 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 20 219 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 219
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 252 3 6 73 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 252 (Polychromatic418967fa.accept_13_3_11_5_1_2348 16 219 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 252 3 5 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 252
  (Polychromatic418967fa.accept_15_14_9_12_1_2498 14 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 219 252 (Polychromatic418967fa.accept_19_13_10_5_1_11329 13 219 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 219 252 3 4 73 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 219 252
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 252 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 219 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 252 3 3 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 252 (Polychromatic418967fa.accept_16_8_11_12_1_962
  8 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 219 252 3 2 73 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 219 252 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 219 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 252 (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 219
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 219 252 3 1 73 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 219 252
  (Polychromatic418967fa.accept_19_2_10_5_1_5639 2 219 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 219 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 219 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 219 252)))))))))))))))))))))))))))))))))) (allB_succ' 35 218 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 218 252 2 17 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 218 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 33 218 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 218 252 2 16 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 218 252 (accept_3_4 31 218 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 218 252 2 15 109 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 218 252
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 29 218 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 218 252 2 14 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 218 252 (Polychromatic418967fa.accept_16_11_10_12_1_4832 27 218 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 218 252 2 13 109 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 218 252 (accept_3_4 25
  218 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 218 252 2 12 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 218 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 218 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 218 252 2 11 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 218 252 (Polychromatic418967fa.accept_13_8_10_5_1_977 21 218 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 218 252 2 10 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 218 252 (accept_3_4 19 218 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 218 252 2 9 109 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 218 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 17 218 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 218 252 2 8 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 218 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 218 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 218 252 2 7 109 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 218 252 (accept_3_4 13 218 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 218 252 2 6 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 218 252
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 218 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 218 252 2 5 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 218 252 (Polychromatic418967fa.accept_25_9_18_2_1_15309 9 218 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 218 252 2 4 109 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 218 252 (accept_3_4 7 218 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 218 252 2 3 109 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 218 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 218 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 218 252 2 2 109 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 218 252 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 218 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 218 252 2 1 109 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 218 252 (accept_3_4 1 218 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 218 252))))))))))))))))))))))))))))))))))) (allB_succ' 36 217 252 (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 217 252 7 5 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 34 217 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 34 217 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 252 (Polychromatic418967fa.accept_15_3_7_12_1_372
  33 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 252 (accept_3_5 32
  217 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 252
  (Polychromatic418967fa.accept_11_9_8_10_1_934 31 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 217 252 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 217 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 252 (accept_3_5 29 217 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 217 252 7 4 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 217 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 27 217 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 252 (accept_3_5 26 217 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 217
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 24 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 252 (accept_3_5 23 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 252 (Polychromatic418967fa.accept_19_3_8_5_1_1875 22 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 217 252 7 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 217 252 (accept_3_5 20 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 217 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 217 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 252 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 217
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 252 (accept_3_5 17 217
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 16 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 217 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 217 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 217 252 7 2 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 217 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 13
  217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 252
  (Polychromatic418967fa.accept_19_12_8_5_1_8538 12 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 252 (accept_3_5 11 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 252 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 217 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 252 (accept_3_5 8 217 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 217 252 7 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 217 252 (Polychromatic418967fa.accept_15_6_7_12_1_869 6 217 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 252 (accept_3_5 5 217 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 217 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 252
  (Polychromatic418967fa.accept_13_3_9_5_1_2340 3 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 252 (accept_3_5 2 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 252 (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 217 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 252)))))))))))))))))))))))))))))))))))) (allB_succ' 37 216 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 216 252 36 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 216 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 216 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 216 252 2 17 108 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 216 252 3 11 72 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 216 252 4 8 54 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 216 252 6 5 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 216 252 (Polychromatic418967fa.accept_13_3_8_5_1_974 29 216 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 252 4 7 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 216 252 9 3 24 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 216 252 2 13 108 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 216 252
  (Polychromatic418967fa.accept_11_3_7_10_1_180 25 216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 216 252 12 2 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 216 252 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 216 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 252 2 11 108 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 216 252 3 7 72 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 216 252 4 5 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 216 252
  (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 216 252 18 1 12 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 216 252 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 216 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 252 4 4 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 216 252 3 5 72 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 216 252 2 7 108 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 252
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 13 216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 216 252 12 1 18 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 216 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 216 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 216 252 2 5 108 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 216 252 9 1 24 28 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 216 252 4 2 54 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 252
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 252 6 1 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 252 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 216 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 252 4 1 54 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 216 252 3 1 72 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 252 2 1 108 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 1
  216 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216
  252))))))))))))))))))))))))))))))))))))) (allB_succ' 38 215 252 (Eq.refl Bool.true) (allA_succ_of_accept 37 215 252
  (accept_3_4 37 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 252
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 215 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 215 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 252 (accept_3_4 34 215 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 215 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 215 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 252 (Polychromatic418967fa.accept_15_2_5_12_1_369
  32 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 252 (accept_3_4 31
  215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 252
  (Polychromatic418967fa.accept_19_11_6_5_1_11299 30 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 215 252 (Polychromatic418967fa.accept_17_12_11_14_1_3120 29 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 252 (accept_3_4 28 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 215 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 215 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 252
  (Polychromatic418967fa.accept_19_7_6_5_1_4320 26 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 215 252 (accept_3_4 25 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 215 252 (Polychromatic418967fa.accept_13_11_7_5_1_2314 24 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 215 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 215 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 252 (accept_3_4 22 215 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 215 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 252
  (Polychromatic418967fa.accept_16_4_7_12_1_2734 20 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 215 252 (accept_3_4 19 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 215 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 215 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 252 (accept_3_4 16 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 252 (Polychromatic418967fa.accept_13_2_7_5_1_3189 15 215
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 252
  (Polychromatic418967fa.accept_19_14_6_5_1_9917 14 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 252 (accept_3_4 13 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 252 (Polychromatic418967fa.accept_13_12_7_5_1_3147 12 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 215 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 252 (accept_3_4 10 215 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 252 (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 252
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 252 (accept_3_4 7 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 252 (Polychromatic418967fa.accept_15_6_5_12_1_1642 6 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 252 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 252 (accept_3_4 4 215 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 215 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 252
  (Polychromatic418967fa.accept_13_2_7_5_1_3189 2 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 252 (accept_3_4 1 215 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  252)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 214 252 (Eq.refl Bool.true) (allA_succ_of_gcd 38 214 252 2 19
  107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214
  252 (Polychromatic418967fa.accept_10_7_4_2_1_903 37 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 214 252 2 18 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 214 252 (accept_3_5 35 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 252 2 17 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 252 (Polychromatic418967fa.accept_27_6_25_9_1_15402 33 214 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 252 2 16 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 252
  (Polychromatic418967fa.accept_15_1_4_12_1_2401 31 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 252 2 15 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 252 (accept_3_5 29 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 252 2 14 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 252 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 214 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 252 2 13 107 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 252
  (Polychromatic418967fa.accept_13_12_6_5_1_2335 25 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 252 2 12 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 252 (accept_3_5 23 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 252 2 11 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 252 (Polychromatic418967fa.accept_23_21_7_22_1_15401 21 214 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 252 2 10 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 252
  (Polychromatic418967fa.accept_25_19_14_2_1_15400 19 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 214 252 2 9 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 214 252 (accept_3_5 17 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 252 2 8 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 252 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 214 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 252 2 7 107 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 252
  (Polychromatic418967fa.accept_17_13_10_14_1_4211 13 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 214 252 2 6 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 214 252 (accept_3_5 11 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 252 2 5 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 252 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 214 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 252 2 4 107 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 252
  (Polychromatic418967fa.accept_10_7_4_2_1_903 7 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 252 2 3 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 252 (accept_3_5 5 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 252 2 2 107 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 252 (Polychromatic418967fa.accept_13_3_6_5_1_2336 3 214 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 252 2 1 107 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 252
  (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 214 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 252))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 213 252 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 213 252 3 13 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 213 252 (Polychromatic418967fa.accept_11_5_4_10_1_524 38 213 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 213
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 213 252 3 12 71 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 213 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 213 252 (Polychromatic418967fa.accept_19_15_4_5_1_11338 34 213 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 213 252 3 11 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 213 252
  (Polychromatic418967fa.accept_15_2_3_12_1_891 32 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 213 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 213 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 213 252 3 10 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 213 252
  (Polychromatic418967fa.accept_17_12_9_14_1_4283 29 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 213 252 (Polychromatic418967fa.accept_15_13_3_12_1_1609 28 213 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 252 3 9 71 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 26 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 213 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 213 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 213 252 3 8 71 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 213 252
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 213 252 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 213 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 252 3 7 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749
  20 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 252
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 19 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 213 252 3 6 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 213 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 213 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 252
  (Polychromatic418967fa.accept_11_5_4_10_1_524 16 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 252 3 5 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 252 (Polychromatic418967fa.accept_22_14_15_10_1_12213 14 213 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 252
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 213 252 3 4 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 213 252 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 213 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 252
  (Polychromatic418967fa.accept_16_10_5_12_1_4925 10 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 213 252 3 3 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 213 252 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 213 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 252 (Polychromatic418967fa.accept_15_7_3_12_1_365
  7 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 252 3 2 71 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 252
  (Polychromatic418967fa.accept_10_5_3_2_1_899 5 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 252 (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 213 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 252 3 1 71 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 252 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 213 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 1 213 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 213 252)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 212 252 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 212 252 4 10 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 212 252 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 212 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 212 252 2 19 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 212 252 (accept_3_4 37 212 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 212 252 4 9 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 212 252 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 212
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 252 2 17 106 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 252
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 33 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 212 252 4 8 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 212 252 (accept_3_4 31 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  212 252 2 15 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 212 252 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 212 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 252 4 7 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 252 (Polychromatic418967fa.accept_13_1_4_5_1_113
  27 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 212 252 2 13 106 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 212 252
  (accept_3_4 25 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 212 252 4 6 53 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 212 252
  (Polychromatic418967fa.accept_13_10_4_5_1_2331 23 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 212 252 2 11 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 212 252 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 212 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 212 252 4 5 53 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 212 252 (accept_3_4 19 212 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 212 252 2 9 106 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 212 252
  (Polychromatic418967fa.accept_16_1_4_12_1_376 17 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 212 252 4 4 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 212 252 (Polychromatic418967fa.accept_13_2_4_5_1_3152 15 212 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 212 252 2 7 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 212 252 (accept_3_4 13 212 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 212 252 4 3 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 212 252 (Polychromatic418967fa.accept_16_11_4_12_1_1760 11 212
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 252 2 5 106 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 252
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 252 4 2 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 212 252 (accept_3_4 7 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 212
  252 2 3 106 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  212 252 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 212 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 212 252 4 1 53 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 212 252 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 212 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 252 2 1 106 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 252 (accept_3_4 1 212 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 212 252))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 211 252
  (Eq.refl Bool.true) (allA_succ_of_accept 41 211 252 (accept_3_5 41 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 211 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 40 211 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 211 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 211 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 252 (accept_3_5 38 211 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 252 (Polychromatic418967fa.accept_13_11_3_5_1_982
  37 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 252
  (Polychromatic418967fa.accept_10_6_1_2_1_874 36 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 252 (accept_3_5 35 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 34 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 252 (accept_3_5 32 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 211 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 252
  (Polychromatic418967fa.accept_24_6_19_12_1_11904 30 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 211 252 (accept_3_5 29 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 211 252 (Polychromatic418967fa.accept_13_2_3_5_1_2294 28 211 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 252 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 211
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 252 (accept_3_5 26 211
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 252
  (Polychromatic418967fa.accept_16_9_3_12_1_1802 25 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 211 252 (Polychromatic418967fa.accept_13_11_3_5_1_982 24 211 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 252 (accept_3_5 23 211 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 211 252 (Polychromatic418967fa.accept_13_9_3_5_1_1605 22 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 252
  (Polychromatic418967fa.accept_13_8_3_5_1_1636 21 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 252 (accept_3_5 20 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 252 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 252 (Polychromatic418967fa.accept_19_18_2_5_1_5682 18 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 252 (accept_3_5 17 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 16 211
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 252
  (Polychromatic418967fa.accept_8_7_3_4_1_404 15 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 252 (accept_3_5 14 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 252 (Polychromatic418967fa.accept_10_3_1_2_1_521 13 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 252 (accept_3_5 11 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 252 (Polychromatic418967fa.accept_16_10_3_12_1_1758 10 211
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 252
  (Polychromatic418967fa.accept_10_9_1_2_1_522 9 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 252 (accept_3_5 8 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 252 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 252 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 211 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 252 (accept_3_5 5 211 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 252 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 211 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 252
  (Polychromatic418967fa.accept_10_3_1_2_1_521 3 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 252 (accept_3_5 2 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 252 (Polychromatic418967fa.accept_11_1_2_10_1_1426 1 211 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 252)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 210 252 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 210 252 42 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 210 252 (Polychromatic418967fa.accept_16_9_2_12_1_1800 41 210 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 252 2 20 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 210 252 3 13 70 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 210 252 2 19 105 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 252
  (Polychromatic418967fa.accept_17_3_6_14_1_4312 37 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 252 6 6 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 210 252 7 5 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 210 252 2 17 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 210 252 3 11 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 210 252 2 16 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 252 (Polychromatic418967fa.accept_11_9_1_10_1_920 31 210
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 210 252 6 5 35 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 210 252
  (Polychromatic418967fa.accept_13_3_2_5_1_1632 29 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 252 14 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 210 252 3 9 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 210 252 2 13 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 210 252 (Polychromatic418967fa.accept_13_12_2_5_1_1634 25 210 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 210 252 6 4 35 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 252
  (Polychromatic418967fa.accept_13_10_2_5_1_1633 23 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 252 2 11 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 210 252 21 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 252 2 10 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 252 (Polychromatic418967fa.accept_23_19_3_22_1_13660 19 210
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 210 252 6 3 35 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 210 252
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 17 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 252 2 8 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 210 252 3 5 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 210 252 14 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 210 252 (Polychromatic418967fa.accept_11_2_1_10_1_196 13 210 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 252 6 2 35 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 252
  (Polychromatic418967fa.accept_22_11_12_10_1_1424 11 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 210 252 2 5 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 252 3 3 70 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 252 2 4 105 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 210 252 7 1 30 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 210 252 6 1 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 252 (Polychromatic418967fa.accept_20_5_10_12_1_8200 5 210
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 252 2 2 105 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 252 3 1 70 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 252 2 1 105 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 252
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 1 210 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 252))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 209 252 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 209 252 (accept_3_4 43 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 209 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 42 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 209 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 252 (accept_3_4 40 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 209 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 38 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 209 252 (accept_3_4 37 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 209 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 209 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 35 209 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 252 (accept_3_4 34 209 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 252 (Polychromatic418967fa.accept_27_6_20_9_1_15399 33 209
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 209 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 32 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 209 252 (accept_3_4 31 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 209 252 (Polychromatic418967fa.accept_13_4_1_5_1_1628 30 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 209 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 209 252 (accept_3_4 28 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 209 252 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 209 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 209 252
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 209 252 (accept_3_4 25 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 209 252 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 252 (Polychromatic418967fa.accept_20_3_9_12_1_6671 23 209
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 209 252 (accept_3_4 22 209
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 209 252
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 209 252 (Polychromatic418967fa.accept_16_4_1_12_1_1792 20 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 252 (accept_3_4 19 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 209 252 (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 209 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 252
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 252 (accept_3_4 16 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 252 (Polychromatic418967fa.accept_22_15_11_10_1_15317 15 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 209 252 (Polychromatic418967fa.accept_22_14_11_10_1_5824 14 209 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 252 (accept_3_4 13 209 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 252
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 12 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 209 252 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 252 (accept_3_4 10 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 209 252 (Polychromatic418967fa.accept_13_9_1_5_1_964 9 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 252 (Polychromatic418967fa.accept_13_8_1_5_1_3176
  8 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 252 (accept_3_4 7
  209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 252
  (Polychromatic418967fa.accept_13_6_1_5_1_3988 6 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 209 252 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 252 (accept_3_4 4 209 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 209 252 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 209 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 252
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 252 (accept_3_4 1 209 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  252)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 208 252 (Eq.refl Bool.true) (allA_succ_of_gcd 44 208
  252 4 11 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  208 252 (Polychromatic418967fa.accept_17_9_4_14_1_4302 43 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 208 252 2 21 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 208 252 (accept_3_5 41 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 208 252 4 10 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 208 252 (Polychromatic418967fa.accept_19_1_18_5_1_5705 39 208 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 252 2 19 104 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 252
  (Polychromatic418967fa.accept_24_13_16_12_1_10137 37 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 208 252 4 9 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 208 252 (accept_3_5 35 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 208 252 2 17 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 208 252 (Polychromatic418967fa.accept_15_3_13_12_1_348 33 208 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 208 252 4 8 52 63 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 252
  (Polychromatic418967fa.accept_15_1_13_12_1_347 31 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 208 252 2 15 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 208 252 (accept_3_5 29 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 208 252 4 7 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 208 252 (Polychromatic418967fa.accept_29_27_5_20_1_15398 27 208 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 208 252 2 13 104 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 252
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 208 252 4 6 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 208 252 (accept_3_5 23 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  208 252 2 11 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 208 252 (Polychromatic418967fa.accept_19_2_18_5_1_11293 21 208 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 252 4 5 52 63 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 252
  (Polychromatic418967fa.accept_24_19_16_12_1_15397 19 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 208 252 2 9 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 208 252 (accept_3_5 17 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 252 4 4 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 208 252 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 208 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 252 2 7 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 252
  (Polychromatic418967fa.accept_17_13_4_14_1_4272 13 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 208 252 4 3 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 208 252 (accept_3_5 11 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 208 252 2 5 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 208 252 (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 208 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 252 4 2 52 63 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 252 (Polychromatic418967fa.accept_17_7_4_14_1_2106
  7 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 252 2 3 104 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 252
  (accept_3_5 5 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 252 4 1 52 63 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 252
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 208 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 252 2 1 104 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 252 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 208 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 252))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  207 252 (Eq.refl Bool.true) (allA_succ_of_gcd 45 207 252 9 5 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 207 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 43 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 207 252 3 14 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 207 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 207 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 252
  (Polychromatic418967fa.accept_13_1_12_5_1_1601 40 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 207 252 3 13 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 207 252 (Polychromatic418967fa.accept_25_13_7_2_1_15247 38 207 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 252
  (Polychromatic418967fa.accept_19_18_17_5_1_4343 37 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 207 252 9 4 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 207 252 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 207 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 207 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 207 252 3 11 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 207 252 (Polychromatic418967fa.accept_13_6_12_5_1_2304 32 207 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 252
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 31 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 207 252 3 10 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 207 252 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 207 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 28 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 207 252 9 3 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 207 252 (Polychromatic418967fa.accept_19_7_17_5_1_3081 26 207 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 207
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 252 3 8 69 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 252
  (Polychromatic418967fa.accept_11_1_9_10_1_184 23 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 207 252 (Polychromatic418967fa.accept_19_3_17_5_1_955 22 207 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 207 252 3 7 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 207 252 (Polychromatic418967fa.accept_13_7_12_5_1_1603
  20 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 207 252 9 2 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 207 252 (Polychromatic418967fa.accept_13_4_12_5_1_476 17 207 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 207 252 (Polychromatic418967fa.accept_27_16_18_9_1_13489 16
  207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 252 3 5 69 84 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 252
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 252 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 207 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 207 252 3 4 69 84 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 207 252
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 252 (Polychromatic418967fa.accept_27_10_18_9_1_15396 10 207 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 252 9 1 23 28 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 252 (Polychromatic418967fa.accept_11_8_9_10_1_503 8
  207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 252
  (Polychromatic418967fa.accept_13_7_12_5_1_1603 7 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 207 252 3 2 69 84 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 207 252 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 207 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 252 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 207 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 207 252 3 1 69 84 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 252
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 2 207 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 252 (Polychromatic418967fa.accept_11_1_9_10_1_184 1 207 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 252)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 206 252
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 206 252 2 23 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 252 (Polychromatic418967fa.accept_13_6_11_5_1_133 45 206
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 206 252 2 22 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 206 252 (accept_3_4 43
  206 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 206 252 2 21 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 206 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 41 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 206 252 2 20 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 206 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270 39 206 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 206 252 2 19 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 206 252 (accept_3_4 37 206 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 206 252 2 18 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 206 252
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 35 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 206 252 2 17 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 206 252 (Polychromatic418967fa.accept_13_7_11_5_1_2302 33 206 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 206 252 2 16 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 206 252 (accept_3_4 31 206 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 206 252 2 15 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 206 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 29 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 206 252 2 14 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 206 252 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 206 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 206 252 2 13 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 206 252 (accept_3_4 25 206 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 206 252 2 12 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 206 252
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 23 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 206 252 2 11 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 206 252 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 206 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 206 252 2 10 103 126 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 206 252 (accept_3_4 19 206 252
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 206 252 2 9 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 206 252
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 17 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 206 252 2 8 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 206 252 (Polychromatic418967fa.accept_20_15_6_12_1_2446 15 206 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 206 252 2 7 103 126 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 206 252 (accept_3_4 13
  206 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 206 252 2 6 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 206 252
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 206 252 2 5 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 206 252 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 206 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 206 252 2 4 103 126 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 206 252 (accept_3_4 7 206 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 206 252 2 3 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 206 252 (Polychromatic418967fa.accept_17_5_2_14_1_4270
  5 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 252 2 2 103 126
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 252
  (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 252 2 1 103 126 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 252 (accept_3_4 1 206 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  252))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 205 252 (Eq.refl Bool.true) (allA_succ_of_accept 47
  205 252 (accept_3_5 47 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 252
  (Polychromatic418967fa.accept_20_6_5_12_1_8169 46 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 205 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 45 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 205 252 (accept_3_5 44 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 205 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 205 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 252
  (Polychromatic418967fa.accept_16_10_13_12_1_4873 42 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 205 252 (accept_3_5 41 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 205 252 (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 205 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 205 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 205 252 (accept_3_5 38 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 205 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 37 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 252 (Polychromatic418967fa.accept_11_3_7_10_1_180 36 205
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 205 252 (accept_3_5 35 205
  252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 205 252
  (Polychromatic418967fa.accept_13_8_10_5_1_977 34 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 205 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 252 (accept_3_5 32 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 205 252 (Polychromatic418967fa.accept_16_15_13_12_1_1787 31 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 252
  (Polychromatic418967fa.accept_13_4_10_5_1_1644 30 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 252 (accept_3_5 29 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 252 (accept_3_5 26 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 205 252
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 252
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 24 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 205 252 (accept_3_5 23 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 205 252 (Polychromatic418967fa.accept_15_7_10_12_1_2403 22 205 252 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 252 (Polychromatic418967fa.accept_13_8_10_5_1_977
  21 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 252 (accept_3_5 20
  205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 252
  (Polychromatic418967fa.accept_13_6_10_5_1_1648 19 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 205 252 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 205 252 (accept_3_5 17 205 252 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 205 252 (Polychromatic418967fa.accept_22_16_7_10_1_7356 16 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 205 252
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 15 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 205 252 (accept_3_5 14 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 205 252 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 205 252 (Polychromatic418967fa.accept_19_12_15_5_1_8600 12 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 252 (accept_3_5 11 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 205 252 (Polychromatic418967fa.accept_16_10_13_12_1_4873 10
  205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 252
  (Polychromatic418967fa.accept_8_1_5_4_1_388 9 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 205 252 (accept_3_5 8 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  205 252 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 205 252 (Polychromatic418967fa.accept_13_6_10_5_1_1648 6 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 252 (accept_3_5 5 205 252 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 252 (Polychromatic418967fa.accept_13_4_10_5_1_1644 4 205
  252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 252
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 205 252 (accept_3_5 2 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  205 252 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 205 252 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 205 252))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_252_segment_002)))))))))))))))))))))))))))))))))))))))))))))))


