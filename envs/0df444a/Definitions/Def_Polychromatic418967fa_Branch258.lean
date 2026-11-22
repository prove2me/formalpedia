-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch258
-- name    : Polychromatic418967fa_Branch258
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:29:26.567754+00:00
-- url     : https://prove2.me/theorems/23876e19-a017-418a-bb81-4a6184bef61d
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch258_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_258 : allB 258 258 :=
  allB_succ' 2 257 258 (Eq.refl Bool.true) (allA_succ_of_accept 1 257 258 (accept_3_4 1 257 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 257 258)) (allB_succ' 3 256 258 (Eq.refl Bool.true) (allA_succ_of_gcd 2 256 258 2 1 128
  129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 256 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 256 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 256 258))) (allB_succ' 4 255 258 (Eq.refl Bool.true) (allA_succ_of_gcd 3 255 258 3 1 85 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 255 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 255 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 255 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 255 258)))) (allB_succ' 5 254 258 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  254 258 2 2 127 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 254 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 254 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 254 258 2 1 127 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 254 258 (accept_3_4 1 254 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 254 258))))) (allB_succ' 6 253 258 (Eq.refl Bool.true) (allA_succ_of_accept 5 253 258
  (accept_3_5 5 253 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 253 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 253 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 253 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 258 (accept_3_5 2 253 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 253 258 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 253 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 258)))))) (allB_succ' 7 252 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 252 258 6 1 42 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 252 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 252 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 252 258 2 2 126 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 252 258 3 1 84 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 252 258 2 1 126 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 258
  (Polychromatic418967fa.accept_16_1_12_2_1_2136 1 252 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 258))))))) (allB_succ' 8 251 258 (Eq.refl Bool.true) (allA_succ_of_accept 7 251 258 (accept_3_4 7 251
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 258
  (Polychromatic418967fa.accept_13_6_4_11_1_282 6 251 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 251 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 251 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 258 (accept_3_4 4 251 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 251 258 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 251 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 2
  251 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 258 (accept_3_4 1 251
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251 258)))))))) (allB_succ' 9 250 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 250 258 2 4 125 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 250 258 (Polychromatic418967fa.accept_13_7_3_11_1_280 7 250 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 250 258 2 3 125 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 250 258 (accept_3_5 5 250 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 250 258 2 2 125 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 250 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 3
  250 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 250 258 2 1 125 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 250 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 258))))))))) (allB_succ' 10 249 258 (Eq.refl Bool.true) (allA_succ_of_gcd 9 249 258 3 3 83 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 249 258
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 249 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 249 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 249 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 249 258 3 2 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 249 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 249 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 258
  (Polychromatic418967fa.accept_10_4_9_8_1_125 4 249 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 249 258 3 1 83 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 249 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 249 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 249 258 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 249 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 249 258)))))))))) (allB_succ' 11 248 258
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 248 258 2 5 124 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 248 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 248 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 248 258 2 4 124 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 248 258 (accept_3_4 7
  248 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 248 258 2 3 124 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 248 258
  (Polychromatic418967fa.accept_15_5_8_3_1_556 5 248 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 248 258 2 2 124 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 248 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 248 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 248 258 2 1 124 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 248 258 (accept_3_4 1 248 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 248 258))))))))))) (allB_succ' 12 247 258 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 247 258 (accept_3_5 11 247 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 247 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 247 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 247 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 247 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 258 (accept_3_5 8 247 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 258 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 247 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 258
  (Polychromatic418967fa.accept_17_6_9_3_1_704 6 247 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 258 (accept_3_5 5 247 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 247 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 247 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 258 (accept_3_5 2 247 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 247 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 258)))))))))))) (allB_succ' 13 246 258 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 246 258 6 2 41 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 246 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 246 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 258 2 5 123 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 246 258 3 3 82 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 246 258 2 4 123 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 246 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 258 6 1 41 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 246 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 246 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 258 2 2 123 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 246 258 3 1 82 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 246 258 2 1 123 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 258
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 246 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 258))))))))))))) (allB_succ' 14 245 258 (Eq.refl Bool.true) (allA_succ_of_accept 13 245 258 (accept_3_4
  13 245 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 245 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 245 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 245 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 245 258 (accept_3_4 10 245 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 245 258 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 245 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 8
  245 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 258 (accept_3_4 7 245
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 258
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 245 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 245 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 245 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 245 258 (accept_3_4 4 245 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 245 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 245 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 245 258 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  245 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 258 (accept_3_4 1 245
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 245 258)))))))))))))) (allB_succ' 15 244 258 (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 244 258 2 7 122 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 244 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 244 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 244 258 2 6 122 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 244 258 (accept_3_5 11 244 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 244 258 2 5 122 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 244 258
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 244 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 244 258 2 4 122 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 244 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 244 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 244 258 2 3 122 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 258 (accept_3_5 5 244 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 258 2 2 122 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 244 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 3
  244 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 244 258 2 1 122 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 244 258
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 1 244 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 244 258))))))))))))))) (allB_succ' 16 243 258 (Eq.refl Bool.true) (allA_succ_of_gcd 15 243 258 3 5 81 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 243 258
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 243 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 243 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 243 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 243 258 3 4 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 243 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  243 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 243 258
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 243 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 243 258 3 3 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 243 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 243 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 258 (Polychromatic418967fa.accept_13_7_9_11_1_705 7 243 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 243 258 3 2 81 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 243 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 243 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 243 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 243 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 258 3 1 81 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 258 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 243 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 243 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 243 258)))))))))))))))) (allB_succ' 17 242 258 (Eq.refl Bool.true) (allA_succ_of_gcd 16 242 258 2 8 121 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 258
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 258 2 7 121 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 258 (accept_3_4 13 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 258 2 6 121 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 242 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 258 2 5 121 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 258
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 258 2 4 121 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 258 (accept_3_4 7 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 258 2 3 121 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 242 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 258 2 2 121 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 258
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 258 2 1 121 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 258 (accept_3_4 1 242 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  258))))))))))))))))) (allB_succ' 18 241 258 (Eq.refl Bool.true) (allA_succ_of_accept 17 241 258 (accept_3_5 17 241 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 241 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 16
  241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 241 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 241 258 (accept_3_5 14 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 241 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 241 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 241 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 241 258 (accept_3_5 11 241 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 241 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 241 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 241 258 (accept_3_5 8 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  241 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 241 258 (Polychromatic418967fa.accept_11_6_10_5_1_341 6 241 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 258 (accept_3_5 5 241 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 241 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 241 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 241 258 (accept_3_5 2 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  241 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 241 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 241 258)))))))))))))))))) (allB_succ' 19 240 258 (Eq.refl Bool.true) (allA_succ_of_gcd 18 240
  258 6 3 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  240 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 240 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 240 258 2 8 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 240 258 3 5 80 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 240 258 2 7 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 240 258 (Polychromatic418967fa.accept_19_13_12_11_1_1249 13 240
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 258 6 2 40 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 240 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 240 258 2 5 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 240 258 3 3 80 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 240 258 2 4 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 240 258 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 240 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 258 6 1 40 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 258
  (Polychromatic418967fa.accept_13_5_6_11_1_1933 5 240 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 258 2 2 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 240 258 3 1 80 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 240 258 2 1 120 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 240 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 240 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 258))))))))))))))))))) (allB_succ' 20 239 258
  (Eq.refl Bool.true) (allA_succ_of_accept 19 239 258 (accept_3_4 19 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 239 258 (Polychromatic418967fa.accept_25_18_14_8_1_15757 18 239 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 258 (accept_3_4 16
  239 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 258
  (Polychromatic418967fa.accept_17_15_1_3_1_1488 15 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 239 258 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 239 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 258 (accept_3_4 13 239 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 239 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 239 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 258 (Polychromatic418967fa.accept_9_2_5_6_1_536
  11 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 239 258 (accept_3_4 10
  239 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 239 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 239 258 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 239 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 258 (accept_3_4 7 239 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 239 258 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 239 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 258 (accept_3_4 4 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 239 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 239 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 258 (accept_3_4 1 239 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 258)))))))))))))))))))) (allB_succ' 21 238 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 238 258 2 10 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 238 258 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 238 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 238 258 2 9 119 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 238 258 (accept_3_5 17 238 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 238 258 2 8 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 238 258 (Polychromatic418967fa.accept_12_3_10_6_1_442
  15 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 238 258 2 7 119 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 238 258
  (Polychromatic418967fa.accept_21_13_7_6_1_3656 13 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 238 258 2 6 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 238 258 (accept_3_5 11 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 238 258 2 5 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 238 258 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 238 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 238 258 2 4 119 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 238 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 238 258 2 3 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 238 258 (accept_3_5 5 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 258 2 2 119 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 238 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 258 2 1 119 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 238 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 258))))))))))))))))))))) (allB_succ' 22 237 258 (Eq.refl Bool.true) (allA_succ_of_gcd 21 237 258 3 7 79
  86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 237 258
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 237 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 237 258 3 6 79 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 237 258 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 237 258 3 5 79 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 237 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 237 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 258 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 237 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 237 258 3 4 79 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 237 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 237 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 237 258 3 3 79 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 258 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 237 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 237 258 3 2 79 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 237 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 237 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 258 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 237 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 237 258 3 1 79 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 237 258
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 237 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 237 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 237 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 237 258)))))))))))))))))))))) (allB_succ' 23 236 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 236 258 2 11 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 236 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 236 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 236 258 2 10 118 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 236 258 (accept_3_4 19 236 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 236 258 2 9 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 236 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  236 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 236 258 2 8 118 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 236 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 236 258 2 7 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 236 258 (accept_3_4 13 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 236 258 2 6 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 236 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 236 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 236 258 2 5 118 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 236 258
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 236 258 2 4 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 236 258 (accept_3_4 7 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 236 258 2 3 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 236 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 236 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 236 258 2 2 118 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 236 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 236 258 2 1 118 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 236 258 (accept_3_4 1 236 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 236
  258))))))))))))))))))))))) (allB_succ' 24 235 258 (Eq.refl Bool.true) (allA_succ_of_accept 23 235 258 (accept_3_5 23
  235 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 22 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 235 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 235 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 235 258 (accept_3_5 20 235 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 235 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 235 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 235 258
  (Polychromatic418967fa.accept_19_18_7_11_1_7552 18 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 235 258 (accept_3_5 17 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 235 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 235 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 258 (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 235
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 258 (accept_3_5 14 235
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 258 (Polychromatic418967fa.accept_4_1_3_2_1_3
  13 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 258 (accept_3_5 11 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 235 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 258 (accept_3_5 8 235 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 235 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 258
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 258 (accept_3_5 5 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 235 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 235 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 258 (accept_3_5 2 235 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 235 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 258)))))))))))))))))))))))) (allB_succ' 25 234 258
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 234 258 6 4 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 234 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 234 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 234 258 2 11 117 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 234 258 3 7 78 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 234 258 2 10 117 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 258
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 234 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 258 6 3 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 234 258 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 234 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 234 258 2 8 117 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 234 258 3 5 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 234 258 2 7 117 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 258
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 234 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 258 6 2 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 234 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 234 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 234 258 2 5 117 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 234 258 3 3 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 234 258 2 4 117 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 258
  (Polychromatic418967fa.accept_21_7_3_6_1_8322 7 234 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 258 6 1 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 234 258 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 234 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 234 258 2 2 117 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 234 258 3 1 78 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 234 258 2 1 117 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 258
  (Polychromatic418967fa.accept_19_1_6_11_1_7548 1 234 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 258))))))))))))))))))))))))) (allB_succ' 26 233 258 (Eq.refl Bool.true) (allA_succ_of_accept 25 233 258
  (accept_3_4 25 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 233 258
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 233 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 233 258 (accept_3_4 22 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 233 258 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 233 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 233 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 258 (accept_3_4 19
  233 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 233 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 233 258 (accept_3_4 16 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 233 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 233 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 233 258 (Polychromatic418967fa.accept_9_5_8_6_1_281
  14 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 258 (accept_3_4 13
  233 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 12 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 233 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 233 258 (accept_3_4 10 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 233 258 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 233 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 8
  233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 258 (accept_3_4 7 233
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 258
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 233 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 233 258 (accept_3_4 4 233 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 233 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 233 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 233 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 2
  233 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 258 (accept_3_4 1 233
  258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 233 258)))))))))))))))))))))))))) (allB_succ' 27 232 258
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 232 258 2 13 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 25 232 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 232 258 2 12 116 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 232 258 (accept_3_5 23
  232 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 232 258 2 11 116 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 232 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 232 258 2 10 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 232 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 232 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 232 258 2 9 116 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 232 258 (accept_3_5 17 232 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 232 258 2 8 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 232 258 (Polychromatic418967fa.accept_10_5_2_8_1_135
  15 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 232 258 2 7 116 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 232 258
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 232 258 2 6 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 232 258 (accept_3_5 11 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 232 258 2 5 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 232 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 232 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 258 2 4 116 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 258
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 258 2 3 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 258 (accept_3_5 5 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 258 2 2 116 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 232 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 232 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 258 2 1 116 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 258
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 232 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 232 258))))))))))))))))))))))))))) (allB_succ' 28 231 258 (Eq.refl Bool.true) (allA_succ_of_gcd 27 231 258 3
  9 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 231
  258 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 231 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 231 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 231 258 3 8 77 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 231 258
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 231 258 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 231 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 231 258 3 7 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 231 258 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 231 258
  (Polychromatic418967fa.accept_10_9_1_8_1_755 19 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 231 258 3 6 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 231 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 231 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 258 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 231
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 231 258 3 5 77 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 231 258
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 231 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 231 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 231 258 3 4 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 231 258 (Polychromatic418967fa.accept_15_11_6_3_1_1192
  11 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 258
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 231 258 3 3 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 231 258 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 231 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 231 258 (Polychromatic418967fa.accept_17_7_10_3_1_1421 7 231
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 258 3 2 77 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 231 258 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 231 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 231 258 3 1 77 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 231 258 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 231 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 231 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 231 258)))))))))))))))))))))))))))) (allB_succ' 29 230 258 (Eq.refl Bool.true) (allA_succ_of_gcd 28 230 258
  2 14 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  230 258 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 230 258 2 13 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 230 258 (accept_3_4 25 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 230 258 2 12 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 230 258 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 230 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 230 258 2 11 115 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 230 258
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 230 258 2 10 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 230 258 (accept_3_4 19 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 230 258 2 9 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 230 258 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 230 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 230 258 2 8 115 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 230 258
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 230 258 2 7 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 230 258 (accept_3_4 13 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 230 258 2 6 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 230 258 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 230 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 230 258 2 5 115 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 230 258
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 230 258 2 4 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 230 258 (accept_3_4 7 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 230 258 2 3 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 230 258 (Polychromatic418967fa.accept_20_5_10_18_1_5622 5 230 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 230 258 2 2 115 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 230 258
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 230 258 2 1 115 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 230 258 (accept_3_4 1 230 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 230
  258))))))))))))))))))))))))))))) (allB_succ' 30 229 258 (Eq.refl Bool.true) (allA_succ_of_accept 29 229 258
  (accept_3_5 29 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 229 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 258 (accept_3_5 26 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 229 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 258 (Polychromatic418967fa.accept_10_4_9_8_1_125
  24 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 258 (accept_3_5 23
  229 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 229 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 258 (accept_3_5 20 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 229 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 258 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 258 (accept_3_5 17
  229 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 16 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 229 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 258 (accept_3_5 14 229 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 229 258 (Polychromatic418967fa.accept_14_13_5_6_1_2747 13 229 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 258
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 258 (accept_3_5 11 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 258 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 258 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 258 (accept_3_5 8 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 229 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 258
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 6 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 258 (accept_3_5 5 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 229 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 258 (accept_3_5 2 229 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 229 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 258)))))))))))))))))))))))))))))) (allB_succ' 31 228
  258 (Eq.refl Bool.true) (allA_succ_of_gcd 30 228 258 6 5 38 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 228 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 228 258 2 14 114 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 228 258 3 9 76 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 228 258 2 13 114 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 228 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 258 6 4 38 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 228 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 228 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 258 2 11 114 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 228 258 3 7 76 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 228 258 2 10 114 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 228 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 228 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 228 258 6 3 38 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 228 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 228 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 258 2 8 114 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 228 258 3 5 76 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 228 258 2 7 114 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 228 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 228 258 6 2 38 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 228 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 228 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 228 258 2 5 114 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 228 258 3 3 76 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 228 258 2 4 114 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 228 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 258 6 1 38 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 228 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 258 2 2 114 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 228 258 3 1 76 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 228 258 2 1 114 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 228 258
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 228 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 228 258))))))))))))))))))))))))))))))) (allB_succ' 32 227 258 (Eq.refl Bool.true) (allA_succ_of_accept 31
  227 258 (accept_3_4 31 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 227 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 227 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 227 258 (accept_3_4 28 227 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 227 258 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 227 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 227 258
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 227 258 (accept_3_4 25 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 227 258 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 227 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 227 258 (accept_3_4 22 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 227 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 227 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 227 258
  (Polychromatic418967fa.accept_11_9_7_5_1_749 20 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 227 258 (accept_3_4 19 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 227 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 227 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 227 258 (accept_3_4 16 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 227 258 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 227 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 258
  (Polychromatic418967fa.accept_9_5_2_6_1_265 14 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 227 258 (accept_3_4 13 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 227 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 227 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 227 258 (accept_3_4 10 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 227 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 227 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 227 258
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 227 258 (accept_3_4 7 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  227 258 (Polychromatic418967fa.accept_16_6_3_2_1_3096 6 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 227 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 227 258 (accept_3_4 4 227 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 227 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 227 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 227 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 227 258 (accept_3_4 1 227 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 227
  258)))))))))))))))))))))))))))))))) (allB_succ' 33 226 258 (Eq.refl Bool.true) (allA_succ_of_gcd 32 226 258 2 16 113
  129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 258
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 226 258 2 15 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 226 258 (accept_3_5 29 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 258 2 14 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 258 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 226 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 258 2 13 113 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 258 2 12 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 258 (accept_3_5 23 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 258 2 11 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 226 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 258 2 10 113 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 258
  (Polychromatic418967fa.accept_13_6_5_11_1_1971 19 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 258 2 9 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 258 (accept_3_5 17 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 258 2 8 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 226 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 258 2 7 113 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 258 2 6 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 258 (accept_3_5 11 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 258 2 5 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 258 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 226 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 258 2 4 113 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 258
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 258 2 3 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 258 (accept_3_5 5 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 258 2 2 113 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 226 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 258 2 1 113 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 258
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 226 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 258))))))))))))))))))))))))))))))))) (allB_succ' 34 225 258 (Eq.refl Bool.true) (allA_succ_of_gcd 33 225
  258 3 11 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  225 258 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 225 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 225 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 225 258 3 10 75 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 225 258
  (Polychromatic418967fa.accept_21_8_15_6_1_8247 29 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 225 258 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 225 258 3 9 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 225 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 26
  225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 258
  (Polychromatic418967fa.accept_13_12_4_11_1_1925 25 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 225 258 3 8 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 225 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 225 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 225 258
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 225 258 3 7 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 225 258 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 225 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 225 258 3 6 75 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 225 258
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 225 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 258 3 5 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 258 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 258
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 225 258 3 4 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 225 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 258 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 225
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 225 258 3 3 75 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 225 258
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 225 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 258 3 2 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 225 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 225 258
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 225 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 225 258 3 1 75 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 225 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 225 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 258 (Polychromatic418967fa.accept_18_1_9_6_1_6630 1 225 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 258))))))))))))))))))))))))))))))))))
  (allB_succ' 35 224 258 (Eq.refl Bool.true) (allA_succ_of_gcd 34 224 258 2 17 112 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 224 258
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 224 258 2 16 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 224 258 (accept_3_4 31 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 224 258 2 15 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 224 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 224 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 224 258 2 14 112 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 224 258
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 224 258 2 13 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 224 258 (accept_3_4 25 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 224 258 2 12 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 224 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 224 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 224 258 2 11 112 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 224 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 224 258 2 10 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 224 258 (accept_3_4 19 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 224 258 2 9 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 224 258 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 224 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 224 258 2 8 112 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 224 258
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 224 258 2 7 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 224 258 (accept_3_4 13 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 224 258 2 6 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 224 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 224 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 224 258 2 5 112 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 224 258
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 224 258 2 4 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 224 258 (accept_3_4 7 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 224 258 2 3 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 224 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 224 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 224 258 2 2 112 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 224 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 224 258 2 1 112 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 224 258 (accept_3_4 1 224 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  258))))))))))))))))))))))))))))))))))) (allB_succ' 36 223 258 (Eq.refl Bool.true) (allA_succ_of_accept 35 223 258
  (accept_3_5 35 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 258
  (Polychromatic418967fa.accept_19_15_14_11_1_7682 34 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 223 258 (accept_3_5 32 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 223 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 223 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 223 258 (accept_3_5 29 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 223 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 223 258 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 258 (accept_3_5 26 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 223 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 223 258
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 223 258 (accept_3_5 23 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 223 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 258 (accept_3_5 20 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 223 258
  (Polychromatic418967fa.accept_17_1_2_3_1_4668 18 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 223 258 (accept_3_5 17 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 223 258 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 223 258 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 258 (accept_3_5 14 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 223 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 223 258 (accept_3_5 11 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 223 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 258 (accept_3_5 8 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 258 (Polychromatic418967fa.accept_14_7_13_6_1_1177 7 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 223 258
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 223 258 (accept_3_5 5 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  223 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 223 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 223 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 258 (accept_3_5 2 223 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 223 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223 258)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 222 258 (Eq.refl Bool.true) (allA_succ_of_gcd 36 222 258 6 6 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 222 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 222 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 222 258 2 17 111 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 222 258 3 11 74 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 222 258 2 16 111
  129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 258
  (Polychromatic418967fa.accept_19_12_13_11_1_453 31 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 222 258 6 5 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 222 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 222 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 222 258 2 14 111 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 222 258 3 9 74 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 222 258 2 13 111 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 258
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 258 6 4 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 222 258 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 222 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 222 258 2 11 111 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 222 258 3 7 74 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 222 258 2 10 111 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 258
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 258 6 3 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 222 258 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 222 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 222 258 2 8 111 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 222 258 3 5 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 222 258 2 7 111 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 258
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 222 258 6 2 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 222 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 222 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 222 258 2 5 111 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 222 258 3 3 74 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 222 258 2 4 111 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 258
  (Polychromatic418967fa.accept_13_7_1_11_1_732 7 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 258 6 1 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 222 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 222 258 2 2 111 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 222 258 3 1 74 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 222 258 2 1 111 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 222 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 258))))))))))))))))))))))))))))))))))))) (allB_succ' 38 221 258 (Eq.refl Bool.true) (allA_succ_of_accept
  37 221 258 (accept_3_4 37 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 258
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 221 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 258 (accept_3_4 34 221 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 221 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 221 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 258
  (Polychromatic418967fa.accept_19_13_12_11_1_1249 32 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 221 258 (accept_3_4 31 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 221 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 221 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 221 258 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 221 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 258 (accept_3_4 28 221 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 258 (accept_3_4 25 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 221 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 258 (accept_3_4 22 221 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 221 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 258
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 258 (accept_3_4 19 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 258 (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 221 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 221 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 258 (accept_3_4 16 221 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 221 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 258
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 221 258 (accept_3_4 13 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 221 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 221 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 221 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 258 (accept_3_4 10 221 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 258
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 258 (accept_3_4 7 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 258 (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 221 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 258 (accept_3_4 4 221 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 221 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 258
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 258 (accept_3_4 1 221 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  258)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 220 258 (Eq.refl Bool.true) (allA_succ_of_gcd 38 220 258 2 19
  110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 220
  258 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 220 258 2 18 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 220 258 (accept_3_5 35 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 220 258 2 17 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 220 258 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 220 258 2 16 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 220 258
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 220 258 2 15 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 220 258 (accept_3_5 29 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 220 258 2 14 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 220 258 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 220 258 2 13 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 220 258
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 220 258 2 12 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 220 258 (accept_3_5 23 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 220 258 2 11 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 220 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 220 258 2 10 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 220 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 220 258 2 9 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 220 258 (accept_3_5 17 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 220 258 2 8 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 220 258 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 258 2 7 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 258
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 220 258 2 6 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 220 258 (accept_3_5 11 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 220 258 2 5 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 220 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 258 2 4 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 220 258 2 3 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 220 258 (accept_3_5 5 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 220 258 2 2 110 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 220 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 220 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 220 258 2 1 110 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 220 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 220 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 220 258))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 219 258 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 219 258 3 13 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 219 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 219 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 219 258 3 12 73 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 219 258
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 219 258 3 11 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 219 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 32
  219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 258
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 219 258 3 10 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 219 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 219 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 219 258 3 9 73 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 219 258
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 219 258 3 8 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 219 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 23
  219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 258
  (Polychromatic418967fa.accept_7_1_2_6_1_55 22 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 219 258 3 7 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 219 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 219 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 258 3 6 73 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 258 3 5 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 219 258 3 4 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 219 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 219 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 258 3 3 73 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 258
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 258 3 2 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 219 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 219 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 258 3 1 73 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 219 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 219 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 258))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 218 258 (Eq.refl Bool.true) (allA_succ_of_gcd 40 218 258 2 20 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 218 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 218 258 2 19 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 218 258 (accept_3_4 37 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 218 258 2 18 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 218 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 218 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 218 258 2 17 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 218 258
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 218 258 2 16 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 218 258 (accept_3_4 31 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 218 258 2 15 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 218 258 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 218 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 218 258 2 14 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 218 258
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 218 258 2 13 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 218 258 (accept_3_4 25 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 218 258 2 12 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 218 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 218 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 218 258 2 11 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 218 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 218 258 2 10 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 218 258 (accept_3_4 19 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 218 258 2 9 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 218 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 218 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 218 258 2 8 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 218 258
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 218 258 2 7 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 218 258 (accept_3_4 13 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 218 258 2 6 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 218 258 (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 218 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 218 258 2 5 109 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 218 258
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 218 258 2 4 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 218 258 (accept_3_4 7 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 218 258 2 3 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 218 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 218 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 218 258 2 2 109 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 218 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 218 258 2 1 109 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 218 258 (accept_3_4 1 218 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218
  258))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 217 258 (Eq.refl Bool.true) (allA_succ_of_accept 41 217
  258 (accept_3_5 41 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 217 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 258 (accept_3_5 38 217 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 217 258 (Polychromatic418967fa.accept_19_18_8_11_1_7663 37 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 217 258
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 217 258 (accept_3_5 35 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 217 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 217 258 (Polychromatic418967fa.accept_13_7_9_11_1_705 33 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 258 (accept_3_5 32 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 217 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 258
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 258 (accept_3_5 29 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 258 (Polychromatic418967fa.accept_13_2_9_11_1_258 28 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 258 (accept_3_5 26 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 258
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 258 (accept_3_5 23 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 258 (accept_3_5 20 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 258
  (Polychromatic418967fa.accept_19_18_8_11_1_7663 18 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 217 258 (accept_3_5 17 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 217 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 217 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 217 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 258 (accept_3_5 14 217 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 258 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 258
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 258 (accept_3_5 11 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 258 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 258 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 258 (accept_3_5 8 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 258
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 6 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 258 (accept_3_5 5 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 217 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 258 (accept_3_5 2 217 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 258 (Polychromatic418967fa.accept_13_1_9_11_1_703 1 217 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 258))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 216 258 (Eq.refl Bool.true) (allA_succ_of_gcd 42 216 258 6 7 36 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 216 258
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 216 258 2 20 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 216 258 3 13 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 216 258 2 19 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 258 (Polychromatic418967fa.accept_19_18_7_11_1_7552 37 216
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 258 6 6 36 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 258
  (Polychromatic418967fa.accept_13_9_8_11_1_725 35 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 216 258 2 17 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 216 258 3 11 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 216 258 2 16 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 258 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 216 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 258 6 5 36 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 258
  (Polychromatic418967fa.accept_13_3_8_11_1_1906 29 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 216 258 2 14 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 216 258 3 9 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 216 258 2 13 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 216 258 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 216 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 258 6 4 36 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 258
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 216 258 2 11 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 216 258 3 7 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 216 258 2 10 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 216 258 (Polychromatic418967fa.accept_13_6_8_11_1_5398 19 216 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 258 6 3 36 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 258
  (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 216 258 2 8 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 216 258 3 5 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 216 258 2 7 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 216 258 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 216 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 258 6 2 36 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 258
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 216 258 2 5 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 216 258 3 3 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 216 258 2 4 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 216 258 (Polychromatic418967fa.accept_17_7_12_3_1_4693 7 216 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 258 6 1 36 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 258
  (Polychromatic418967fa.accept_15_5_6_3_1_525 5 216 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 216 258 2 2 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 216 258 3 1 72 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 216 258 2 1 108 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 216 258 (Polychromatic418967fa.accept_13_1_8_11_1_724 1 216 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 258)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 215 258 (Eq.refl Bool.true) (allA_succ_of_gcd 43 215 258 43 1 5 6 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 42 215 258
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 215 258 (accept_3_4 40 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 215 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 215 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 258 (accept_3_4 37
  215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 215 258 (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 215 258 (accept_3_4 34 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 215 258 (Polychromatic418967fa.accept_7_4_5_6_1_344
  32 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 258 (accept_3_4 31
  215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 30 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 215 258 (accept_3_4 28 215 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 215 258 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 215 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 215 258
  (Polychromatic418967fa.accept_17_9_11_3_1_2353 26 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 215 258 (accept_3_4 25 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 215 258 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 215 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 215 258 (accept_3_4 22 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 215 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 258
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 215 258 (accept_3_4 19 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 215 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 215 258 (accept_3_4 16 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 215 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 215 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 215 258
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 215 258 (accept_3_4 13 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 215 258 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 215 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 215 258 (accept_3_4 10 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 215 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 215 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 215 258 (accept_3_4 7 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  215 258 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 215 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 258 (accept_3_4 4 215 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 258 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 215 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 258
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 258 (accept_3_4 1 215 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215
  258)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 214 258 (Eq.refl Bool.true) (allA_succ_of_gcd 44 214
  258 2 22 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  43 214 258 (Polychromatic418967fa.accept_13_4_6_11_1_2017 43 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 214 258 2 21 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 214 258 (accept_3_5 41 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 258 2 20 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 214 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 258 2 19 107 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 258
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 258 2 18 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 258 (accept_3_5 35 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 258 2 17 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 214 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 258 2 16 107 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 258
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 258 2 15 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 258 (accept_3_5 29 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 258 2 14 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 258 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 214 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 258 2 13 107 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 258
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 25 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 258 2 12 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 258 (accept_3_5 23 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 258 2 11 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 214 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 258 2 10 107 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 258 2 9 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 258 (accept_3_5 17 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 258 2 8 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 258 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 214 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 258 2 7 107 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 258
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 258 2 6 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 258 (accept_3_5 11 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 258 2 5 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 214 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 258 2 4 107 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 258
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 258 2 3 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 258 (accept_3_5 5 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 258 2 2 107 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 214 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 258 2 1 107 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 258
  (Polychromatic418967fa.accept_9_1_7_6_1_75 1 214 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 258))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 213 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 213 258 3 15 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 213 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 213 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 213 258 3 14 71 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 213 258
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 213 258 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 213 258 3 13 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 213 258 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 213 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 213 258 3 12 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 213 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 258
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 213 258 3 11 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 213 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 213 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 213 258 3 10 71 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 213 258
  (Polychromatic418967fa.accept_13_3_5_11_1_716 29 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 258 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 258 3 9 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 258 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 258
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 213 258 3 8 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 258 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 213
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 258 3 7 71 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 258
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 258 3 6 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 258
  (Polychromatic418967fa.accept_18_17_15_6_1_1797 17 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 213 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 213 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 213 258 3 5 71 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 213 258
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 213 258 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 258 3 4 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 213 258
  (Polychromatic418967fa.accept_11_10_4_5_1_359 10 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 213 258 3 3 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 213 258 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 213 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 213 258 3 2 71 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 213 258
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 213 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 258 3 1 71 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 213 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 258
  (Polychromatic418967fa.accept_10_1_3_8_1_136 1 213 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 213 258)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 212 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 212 258 2 23 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 212 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 212 258 2 22 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 212 258 (accept_3_4 43 212 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 212 258 2 21 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 212 258 (Polychromatic418967fa.accept_11_8_3_5_1_355
  41 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 212 258 2 20 106 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 212 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 212 258 2 19 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 212 258 (accept_3_4 37 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 212 258 2 18 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 212 258 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 212 258 2 17 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 212 258
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 212 258 2 16 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 212 258 (accept_3_4 31 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 212 258 2 15 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 212 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 212 258 2 14 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 212 258
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 212 258 2 13 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 212 258 (accept_3_4 25 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 212 258 2 12 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 212 258 (Polychromatic418967fa.accept_13_10_4_11_1_1969 23 212 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 212 258 2 11 106 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 212 258
  (Polychromatic418967fa.accept_9_3_5_6_1_253 21 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 212 258 2 10 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 212 258 (accept_3_4 19 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 212 258 2 9 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 212 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 212 258 2 8 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 212 258
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 212 258 2 7 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 212 258 (accept_3_4 13 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 212 258 2 6 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 212 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 212 258 2 5 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 212 258
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 212 258 2 4 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 212 258 (accept_3_4 7 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 212 258 2 3 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 212 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 212 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 212 258 2 2 106 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 212 258
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 212 258 2 1 106 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 212 258 (accept_3_4 1 212 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  258))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 211 258 (Eq.refl Bool.true) (allA_succ_of_accept 47
  211 258 (accept_3_5 47 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 211 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 46 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 211 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 258 (accept_3_5 44 211 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 211 258 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 258
  (Polychromatic418967fa.accept_19_4_2_11_1_3409 42 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 258 (accept_3_5 41 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 258 (accept_3_5 38 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 258
  (Polychromatic418967fa.accept_13_10_3_11_1_1923 36 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 211 258 (accept_3_5 35 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 211 258 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 211 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 211 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 258 (accept_3_5 32 211 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 258
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 31 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 211 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 211 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 211 258 (accept_3_5 29 211 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 211 258 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 211 258
  (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 211 258 (accept_3_5 26 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 211 258 (Polychromatic418967fa.accept_21_3_1_6_1_1162 24 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 211 258 (accept_3_5 23 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 211 258 (Polychromatic418967fa.accept_16_6_3_2_1_3096 22 211
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 211 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 211 258 (accept_3_5 20 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 211 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 211 258 (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 211 258 (accept_3_5 17 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 211 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 211 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 258
  (Polychromatic418967fa.accept_13_2_3_11_1_1287 15 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 211 258 (accept_3_5 14 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 211 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 211 258 (accept_3_5 11 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 211 258 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 211 258 (accept_3_5 8 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  211 258 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 211 258 (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 258 (accept_3_5 5 211 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 258 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 211 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 258
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 258 (accept_3_5 2 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 258)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 210 258 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 210 258 6 8 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 210 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 210 258 2 23 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 210 258 3 15 70 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 210 258 2 22 105 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 258 6 7 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 210 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 210 258 2 20 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 210 258 3 13 70 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 210 258 2 19 105 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 258
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 258 6 6 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 210 258 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 210 258 2 17 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 210 258 3 11 70 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 210 258 2 16 105 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 258 6 5 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 210 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 210 258 2 14 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 210 258 3 9 70 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 210 258 2 13 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 258 6 4 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 210 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 210 258 2 11 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 210 258 3 7 70 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 210 258 2 10 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 258
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 258 6 3 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 210 258 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 210 258 2 8 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 210 258 3 5 70 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 210 258 2 7 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 258 6 2 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 210 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 210 258 2 5 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 210 258 3 3 70 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 258 2 4 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 258
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 258 6 1 35 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 210 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 210 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 210 258 2 2 105 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 210 258 3 1 70 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 258 2 1 105 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 258
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 210 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 258))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 209 258 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 209 258 (accept_3_4 49 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 209 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 209 258 (accept_3_4 46 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 209 258 (Polychromatic418967fa.accept_21_3_20_6_1_5126 45 209 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 209 258
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 209 258 (accept_3_4 43 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 209 258 (Polychromatic418967fa.accept_13_3_1_11_1_1268 42 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 209 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 209 258 (accept_3_4 40 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 209 258
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 38 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 209 258 (accept_3_4 37 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 209 258 (Polychromatic418967fa.accept_13_10_1_11_1_1961 36 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 209 258 (accept_3_4 34
  209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 209 258
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 209 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 32 209 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 258 (accept_3_4 31 209 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 209 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 258
  (Polychromatic418967fa.accept_13_3_1_11_1_1268 29 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 258 (accept_3_4 28 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 258 (accept_3_4 25 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 258 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 258 (accept_3_4 22 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 258 (Polychromatic418967fa.accept_13_7_1_11_1_732 20 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 258 (accept_3_4 19 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 258 (Polychromatic418967fa.accept_21_18_20_6_1_6640 18 209
  258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 258
  (Polychromatic418967fa.accept_9_8_2_6_1_875 17 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 258 (accept_3_4 16 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 258 (accept_3_4 13 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 258 (accept_3_4 10 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 258 (Polychromatic418967fa.accept_13_9_1_11_1_275 9 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 258 (accept_3_4 7 209 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 258 (Polychromatic418967fa.accept_16_6_1_2_1_3129 6 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 258
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 258 (accept_3_4 4 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 258 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 258 (accept_3_4 1 209 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 209 258)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 208
  258 (Eq.refl Bool.true) (allA_succ_of_gcd 50 208 258 2 25 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 208 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 208 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 208 258 2 24 104 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 208 258 (accept_3_5 47
  208 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 208 258 2 23 104 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 208 258
  (Polychromatic418967fa.accept_12_9_4_6_1_460 45 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 208 258 2 22 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 208 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 208 258 2 21 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 208 258 (accept_3_5 41 208 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 208 258 2 20 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 208 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 39
  208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 258 2 19 104 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 258
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 37 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 208 258 2 18 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 208 258 (accept_3_5 35 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 208 258 2 17 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 208 258 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 208 258 2 16 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 31 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 208 258 2 15 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 208 258 (accept_3_5 29 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 208 258 2 14 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 208 258 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 208 258 2 13 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 208 258
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 208 258 2 12 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 208 258 (accept_3_5 23 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 208 258 2 11 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 208 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 258 2 10 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 258
  (Polychromatic418967fa.accept_23_19_1_5_1_15756 19 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 208 258 2 9 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 208 258 (accept_3_5 17 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 258 2 8 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 258 2 7 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 258
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 208 258 2 6 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 208 258 (accept_3_5 11 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 208 258 2 5 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 208 258 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 208 258 2 4 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 208 258
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 208 258 2 3 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 208 258 (accept_3_5 5 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 208 258 2 2 104 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 208 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 208 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 258 2 1 104 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 208 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 258))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 207 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 207 258 3 17 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 207 258 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 207 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 207 258 3 16 69 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 207 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 207 258 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 207 258 3 15 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 44
  207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 258
  (Polychromatic418967fa.accept_13_4_12_11_1_5362 43 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 207 258 3 14 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 207 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 207 258 3 13 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 207 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 207 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 207 258 3 12 69 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 207 258
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 258 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 207 258 3 11 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 207 258 (Polychromatic418967fa.accept_12_8_3_6_1_909
  32 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 258
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 207 258 3 10 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 207 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 258 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 207 258 3 9 69 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 258 3 8 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 258
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 207 258 3 7 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 207 258 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 207 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 258 3 6 69 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 258 3 5 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 258 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 258
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 207 258 3 4 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 207 258 (Polychromatic418967fa.accept_20_11_7_18_1_8632 11 207 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 258 (Polychromatic418967fa.accept_7_3_4_6_1_329
  10 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 258 3 3 69 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 258
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 258 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 258 3 2 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 258
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 207 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 207 258 3 1 69 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 207 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 207 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  258)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 206 258 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 206 258 2 26 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 206 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 206 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 206 258 2 25 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 206 258 (accept_3_4 49 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 206 258 2 24 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 206 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 206 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 206 258 2 23 103 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 206 258
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 206 258 2 22 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 206 258 (accept_3_4 43 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 206 258 2 21 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 206 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 206 258 2 20 103 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 206 258
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 206 258 2 19 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 206 258 (accept_3_4 37 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 206 258 2 18 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 206 258 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 206 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 206 258 2 17 103 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 206 258
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 206 258 2 16 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 206 258 (accept_3_4 31 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 206 258 2 15 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 206 258 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 206 258 2 14 103 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 206 258
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 206 258 2 13 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 206 258 (accept_3_4 25 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 206 258 2 12 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 206 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 206 258 2 11 103 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 206 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 206 258 2 10 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 206 258 (accept_3_4 19 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 206 258 2 9 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 206 258 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 206 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 206 258 2 8 103 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 206 258
  (Polychromatic418967fa.accept_12_3_2_6_1_138 15 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 206 258 2 7 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 206 258 (accept_3_4 13 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 206 258 2 6 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 258 2 5 103 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 258 2 4 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 258 (accept_3_4 7 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 258 2 3 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 258 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 206 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 258 2 2 103 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 258
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 258 2 1 103 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 258 (accept_3_4 1 206 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  258))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 205 258 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 205 258 (accept_3_5 53 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 205 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 205 258 (accept_3_5 50 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 205 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 205 258 (accept_3_5 47 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 205 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 205 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 205 258 (accept_3_5 44 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 258
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 205 258 (accept_3_5 41 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 205 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 258 (accept_3_5 38 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 258
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 258 (accept_3_5 35 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 258 (Polychromatic418967fa.accept_13_8_10_11_1_2730 34 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 258 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 258 (accept_3_5 32 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 205 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 258 (accept_3_5 29 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 258 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 258 (accept_3_5 26 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 258
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 258 (accept_3_5 23 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 258 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 258 (accept_3_5 20 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 258
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 258 (accept_3_5 17 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 258 (Polychromatic418967fa.accept_13_3_10_11_1_1293 16 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 258 (accept_3_5 14 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 258 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 258
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 258 (accept_3_5 11 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 258 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 258 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 258 (accept_3_5 8 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 258
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 258 (accept_3_5 5 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 258 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 205 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 258 (accept_3_5 2 205 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 258 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  258)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 204 258 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 204 258 6 9 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 204 258 (Polychromatic418967fa.accept_13_1_9_11_1_703 53 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 204 258 2 26 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 204 258 3 17 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 204 258 2 25 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 258
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 258 6 8 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 204 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 204 258 2 23 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 204 258 3 15 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 204 258 2 22 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 258
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 258 6 7 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 204 258 (Polychromatic418967fa.accept_13_2_9_11_1_258 41 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 204 258 2 20 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 204 258 3 13 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 204 258 2 19 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 258
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 258 6 6 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 258 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 204 258 2 17 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 204 258 3 11 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 204 258 2 16 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 258
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 31 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 204 258 6 5 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 204 258 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 204 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 258 2 14 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 204 258 3 9 68 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 204 258 2 13 102 129 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 204 258
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 204 258 6 4 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 204 258 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 258 2 11 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 204 258 3 7 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 204 258 2 10 102 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 204 258
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 204 258 6 3 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 204 258 (Polychromatic418967fa.accept_16_1_12_2_1_2136 17 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 258 2 8 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 204 258 3 5 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 258 2 7 102 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 258
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 258 6 2 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 258 (Polychromatic418967fa.accept_21_11_15_6_1_3667 11 204 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 204 258 2 5 102 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 204 258 3 3 68 86 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 258 2 4 102 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 258
  (Polychromatic418967fa.accept_13_7_9_11_1_705 7 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 258 6 1 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 258 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 204 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 258 2 2 102 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 258 3 1 68 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 258 2 1 102 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 258
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 204 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 258))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 203 258 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 203 258 (accept_3_4 55 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 203 258 (Polychromatic418967fa.accept_15_9_8_3_1_557 54 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 203 258 (accept_3_4 52 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 203 258 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 258
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 203 258 (accept_3_4 49 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 203 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 203 258 (Polychromatic418967fa.accept_9_2_5_6_1_536 47 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 203 258 (accept_3_4 46 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 203 258
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 203 258 (accept_3_4 43 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 203 258 (Polychromatic418967fa.accept_13_3_8_11_1_1906 42 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 203 258 (accept_3_4 40 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 203 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 203 258
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 203 258 (accept_3_4 37 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 203 258 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 203 258 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 203 258 (accept_3_4 34 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 203 258
  (Polychromatic418967fa.accept_13_6_8_11_1_5398 32 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 203 258 (accept_3_4 31 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 203 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 203 258 (accept_3_4 28 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 258 (Polychromatic418967fa.accept_13_1_8_11_1_724 27 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 258
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 258 (accept_3_4 25 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 258 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 258 (Polychromatic418967fa.accept_13_10_8_11_1_1985 23 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 258 (accept_3_4 22 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 203 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 258
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 258 (accept_3_4 19 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 258 (Polychromatic418967fa.accept_21_18_14_6_1_8278 18 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 258 (accept_3_4 16 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 258 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 258
  (Polychromatic418967fa.accept_13_1_8_11_1_724 14 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 258 (accept_3_4 13 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 258 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 258 (accept_3_4 10 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 258
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 258 (accept_3_4 7 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 258 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 258 (accept_3_4 4 203 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 258 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 203 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 258
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 258 (accept_3_4 1 203 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  258)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 202 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 202 258 2 28 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 202 258 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 202 258 2 27 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 202 258 (accept_3_5 53 202 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 202 258 2 26 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 202 258 (Polychromatic418967fa.accept_12_3_10_6_1_442
  51 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 258 2 25 101 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 258
  (Polychromatic418967fa.accept_15_4_7_3_1_119 49 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 202 258 2 24 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 202 258 (accept_3_5 47 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 258 2 23 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 258 2 22 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 43 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 258 2 21 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 258 (accept_3_5 41 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 258 2 20 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 39 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 258 2 19 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 37 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 258 2 18 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 258 (accept_3_5 35 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 258 2 17 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 258 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 202 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 258 2 16 101 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 258
  (Polychromatic418967fa.accept_13_5_7_11_1_3470 31 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 258 2 15 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 258 (accept_3_5 29 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 258 2 14 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 258 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 202 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 258 2 13 101 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 25 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 258 2 12 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 258 (accept_3_5 23 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 258 2 11 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 258 2 10 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 258 2 9 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 258 (accept_3_5 17 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 258 2 8 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 258 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 258 2 7 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 258
  (Polychromatic418967fa.accept_19_13_12_11_1_1249 13 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 202 258 2 6 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 202 258 (accept_3_5 11 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 258 2 5 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 258 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 258 2 4 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 258
  (Polychromatic418967fa.accept_9_7_4_6_1_273 7 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 258 2 3 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 258 (accept_3_5 5 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 258 2 2 101 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 258 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 202 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 258 2 1 101 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 258
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 202 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 258))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 201 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 201 258 3 19 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 201 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 201 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 201 258 3 18 67 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 201 258
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 201 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 201 258 3 17 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 201 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 201 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 201 258 3 16 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 201 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 258 (Polychromatic418967fa.accept_7_4_5_6_1_344
  46 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 201 258 3 15 67 86
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 201 258
  (Polychromatic418967fa.accept_9_8_3_6_1_533 44 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 201 258 3 14 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 201 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 201 258 3 13 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 201 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 38 201 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 37
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 201 258 3 12 67 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 201 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 201 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 34 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 201 258 3 11 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 201 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 32
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 258
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 201 258 3 10 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 201 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 201 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 258 3 9 67 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 258
  (Polychromatic418967fa.accept_9_8_3_6_1_533 26 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 201 258 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 201 258 3 8 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 201 258 3 7 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 201 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 201 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 258 3 6 67 86 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 258
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 201 258 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 201 258 3 5 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 201 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 258
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 201 258 3 4 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 258 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 201 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 258 3 3 67 86 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 258
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 258 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 258 3 2 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 258 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 201 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 258
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 201 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 201 258 3 1 67 86 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 201 258 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 201 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 258 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 201 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  258)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 200 258 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 200 258 2 29 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 200 258 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 200 258 2 28 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 200 258 (accept_3_4 55 200 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 200 258 2 27 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 200 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 53
  200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 200 258 2 26 100 129
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 200 258
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 200 258 2 25 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 200 258 (accept_3_4 49 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 200 258 2 24 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 200 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 200 258 2 23 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 200 258
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 200 258 2 22 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 200 258 (accept_3_4 43 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 200 258 2 21 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 200 258 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 200 258 2 20 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 200 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 39 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 200 258 2 19 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 200 258 (accept_3_4 37 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 200 258 2 18 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 200 258 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 200 258 2 17 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 200 258
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 200 258 2 16 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 200 258 (accept_3_4 31 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 200 258 2 15 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 200 258 (Polychromatic418967fa.accept_13_3_5_11_1_716 29 200 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 200 258 2 14 100 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 200 258
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 200 258 2 13 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 200 258 (accept_3_4 25 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 200 258 2 12 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 200 258 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 200 258 2 11 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 200 258
  (Polychromatic418967fa.accept_9_3_2_6_1_264 21 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 200 258 2 10 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 200 258 (accept_3_4 19 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 200 258 2 9 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 200 258 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 258 2 8 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 258
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 258 2 7 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 258 (accept_3_4 13 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 258 2 6 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 258 (Polychromatic418967fa.accept_22_11_2_16_1_759 11 200 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 258 2 5 100 129 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 258
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 258 2 4 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 258 (accept_3_4 7 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 258 2 3 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 258 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 200 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 258 2 2 100 129 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 258
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 258 2 1 100 129 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 258 (accept_3_4 1 200 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  258))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 199 258 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 199 258 (accept_3_5 59 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 258 (accept_3_5 56 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 258 (Polychromatic418967fa.accept_19_17_9_11_1_6057 55 199 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 258
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 258 (accept_3_5 53 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 258 (accept_3_5 50 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 258
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 258 (accept_3_5 47 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 258 (accept_3_5 44 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 258
  (Polychromatic418967fa.accept_17_8_12_3_1_5927 42 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 258 (accept_3_5 41 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 258 (accept_3_5 38 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 258
  (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 199 258 (accept_3_5 35 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 199 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 199 258 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 199 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 258 (accept_3_5 32 199 258
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 258 (Polychromatic418967fa.accept_9_4_1_6_1_284
  31 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 258
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 258 (accept_3_5 29 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 258 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 258 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 258 (accept_3_5 26 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 199 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 258
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 258 (accept_3_5 23 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 258 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 258 (accept_3_5 20 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 258 (Polychromatic418967fa.accept_13_6_4_11_1_282 19 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 258
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 258 (accept_3_5 17 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 258 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 258 (Polychromatic418967fa.accept_13_2_4_11_1_2003 15 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 258 (accept_3_5 14 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 258
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 258
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 258 (accept_3_5 11 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 258 (Polychromatic418967fa.accept_13_10_4_11_1_1969 10 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 258 (accept_3_5 8 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 258 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 258
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 6 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 258 (accept_3_5 5 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 258 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 199 258 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 258 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 258 (accept_3_5 2 199 258 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 258 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 258 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  258))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_258_segment_002)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


