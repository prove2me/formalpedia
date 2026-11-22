-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch268
-- name    : Polychromatic418967fa_Branch268
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:31:20.289435+00:00
-- url     : https://prove2.me/theorems/4419900f-fe69-4505-b287-85cfd9115844
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch268_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_268 : allB 268 268 :=
  allB_succ' 2 267 268 (Eq.refl Bool.true) (allA_succ_of_accept 1 267 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  267 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 267 268)) (allB_succ' 3 266 268
  (Eq.refl Bool.true) (allA_of_3_1 3 266 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 265 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 265 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 265 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 265 268 (accept_3_3 2 265 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 265 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 265 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 265 268)))) (allB_succ' 5 264 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 264 268 4 1 66 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 264 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 264 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 264 268 2 1 132 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 264 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 264
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264 268))))) (allB_succ' 6 263 268 (Eq.refl
  Bool.true) (allA_of_3_1 6 263 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 262 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 262 268 2 3 131 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 262 268 (accept_3_3 5 262 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 262 268 2 2 131 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 262 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 262 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 262 268 2 1 131 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 262 268
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 262 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 262 268))))))) (allB_succ' 8 261 268 (Eq.refl Bool.true) (allA_succ_of_accept 7 261 268
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 261 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 261 268 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 261 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 261 268 (accept_3_3 5 261 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 261 268 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 261 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 261 268 (Polychromatic418967fa.accept_10_3_1_8_1_132 3
  261 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 261 268 (accept_3_3 2 261
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 261 268 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 261 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 261 268)))))))) (allB_succ' 9 260 268
  (Eq.refl Bool.true) (allA_of_3_1 9 260 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 259 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 259 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 259 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 268 (accept_3_3 8 259 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 259 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 259 268
  (Polychromatic418967fa.accept_15_6_4_13_1_403 6 259 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 259 268 (accept_3_3 5 259 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  259 268 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 259 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 259 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 259 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 268 (accept_3_3 2 259 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 268 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 259 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 259 268)))))))))) (allB_succ' 11 258 268 (Eq.refl
  Bool.true) (allA_succ_of_gcd 10 258 268 2 5 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 258 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 258 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 258 268 2 4 129 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 268
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 7 258 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 258 268 2 3 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 258 268 (accept_3_3 5 258 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 258 268 2 2 129 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 258 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 258 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 258 268 2 1 129 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 258 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 258 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 258 268))))))))))) (allB_succ' 12 257 268 (Eq.refl Bool.true) (allA_of_3_1 12 257 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 256 268 (Eq.refl Bool.true) (allA_succ_of_gcd 12 256 268 4 3 64 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 256 268 (accept_3_3 11
  256 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 256 268 2 5 128 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 256 268
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 256 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 256 268 4 2 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 256 268 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 256 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 256 268 2 3 128 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 256 268 (accept_3_3 5 256 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 256 268 4 1 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 256 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 256 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 256 268 2 1 128 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 256 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 256 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 256 268))))))))))))) (allB_succ' 14 255 268 (Eq.refl Bool.true) (allA_succ_of_accept 13 255 268
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 255 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 255 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 255 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 255 268 (accept_3_3 11 255 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 255 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 255 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 255 268 (Polychromatic418967fa.accept_11_9_2_4_1_707 9
  255 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 255 268 (accept_3_3 8 255
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 268 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 255 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 255 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 255 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 255 268 (accept_3_3 5 255 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  255 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 255 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 255 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 255 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 255 268 (accept_3_3 2 255 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 255 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 255 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 255 268)))))))))))))) (allB_succ' 15 254 268 (Eq.refl
  Bool.true) (allA_of_3_1 15 254 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 253 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 253 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 268 (accept_3_3 14 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 253 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 253 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 253 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  253 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 268 (accept_3_3 11
  253 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 268
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 253 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 253 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 253 268 (accept_3_3 8 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 253 268 (Polychromatic418967fa.accept_18_7_1_16_1_578 7 253 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 253 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  253 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 268 (accept_3_3 5 253
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 268
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 253 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 253 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 268 (accept_3_3 2 253 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 253 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 253 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 268)))))))))))))))) (allB_succ' 17 252 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 252 268 4 4 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 252 268 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 252 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 252 268 2 7 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 268
  (Polychromatic418967fa.accept_24_13_12_4_1_2746 13 252 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 252 268 4 3 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 252 268 (accept_3_3 11 252 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 252 268 2 5 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 252 268 (Polychromatic418967fa.accept_25_9_2_18_1_16389 9 252 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 252 268 4 2 63 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 268
  (Polychromatic418967fa.accept_19_7_5_2_1_2842 7 252 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 252 268 2 3 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 252 268 (accept_3_3 5 252 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 252 268 4 1 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 252 268 (Polychromatic418967fa.accept_13_3_5_8_1_1099 3 252 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 252 268 2 1 126 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 268 (Polychromatic418967fa.accept_13_1_5_8_1_207 1
  252 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252 268))))))))))))))))) (allB_succ' 18
  251 268 (Eq.refl Bool.true) (allA_of_3_1 18 251 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 250 268
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 250 268 2 9 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 250 268 (accept_3_3 17 250 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 250 268 2 8 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 250 268 (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 250 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 250 268 2 7 125 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 250 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 250 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 250 268 2 6 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 250 268 (accept_3_3 11 250 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 250 268 2 5 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 250 268 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 250 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 250 268 2 4 125 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 250 268
  (Polychromatic418967fa.accept_11_7_8_4_1_718 7 250 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 250 268 2 3 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 250 268 (accept_3_3 5 250 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 250 268 2 2 125 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 250 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 250 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 250 268 2 1 125 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 268
  (Polychromatic418967fa.accept_11_1_8_4_1_717 1 250 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 268))))))))))))))))))) (allB_succ' 20 249 268 (Eq.refl Bool.true) (allA_succ_of_accept 19 249 268
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 249 268 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 249 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 249 268 (accept_3_3 17 249 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 249 268 (Polychromatic418967fa.accept_23_16_19_15_1_14746 16 249 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 249 268
  (Polychromatic418967fa.accept_17_15_11_13_1_2039 15 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 249 268 (accept_3_3 14 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 249 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 249 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 249 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 249 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 249 268 (accept_3_3 11 249 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 249 268 (Polychromatic418967fa.accept_9_1_6_7_1_285
  10 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 249 268
  (Polychromatic418967fa.accept_14_9_11_2_1_2501 9 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 249 268 (accept_3_3 8 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  249 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 249 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 249 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 249 268 (accept_3_3 5 249 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 249 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 249 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 249 268 (accept_3_3 2 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  249 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 249 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 249 268)))))))))))))))))))) (allB_succ' 21 248 268 (Eq.refl Bool.true) (allA_of_3_1 21 248 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 247 268 (Eq.refl Bool.true) (allA_succ_of_accept 21 247 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 247 268 (accept_3_3 20 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 247 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 247 268 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 247 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 268 (accept_3_3 17 247 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 247 268 (Polychromatic418967fa.accept_17_16_9_13_1_3087 16 247 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 268 (accept_3_3 14 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 247 268 (Polychromatic418967fa.accept_25_13_22_18_1_12963 13 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 247 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 247 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 268 (accept_3_3 11 247 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 247 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 268 (accept_3_3 8 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 268 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 268 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 247 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 268 (accept_3_3 5 247 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 268 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 247 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 268 (accept_3_3 2 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 247 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 268)))))))))))))))))))))) (allB_succ' 23 246 268 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  246 268 2 11 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 246 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 246 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 246 268 2 10 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 246 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 19
  246 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 246 268 2 9 123 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 246 268 (accept_3_3 17
  246 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 268 2 8 123 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 246 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 246 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 246 268 2 7 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 246 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 246 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 246 268 2 6 123 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 246 268 (accept_3_3 11 246 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 268 2 5 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 246 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 9
  246 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 246 268 2 4 123 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 268
  (Polychromatic418967fa.accept_13_7_12_8_1_199 7 246 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 268 2 3 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 246 268 (accept_3_3 5 246 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 246 268 2 2 123 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 246 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 246 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 246 268 2 1 123 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 268
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 246 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 268))))))))))))))))))))))) (allB_succ' 24 245 268 (Eq.refl Bool.true) (allA_of_3_1 24 245 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 244 268 (Eq.refl Bool.true) (allA_succ_of_gcd 24 244 268 4 6 61 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 244 268
  (accept_3_3 23 244 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 244 268 2 11 122 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 244 268
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 244 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 244 268 4 5 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 244 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 19 244 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 244 268 2 9 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 244 268 (accept_3_3 17 244 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 244 268 4 4 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 244 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 244 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 244 268 2 7 122 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 244 268
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 244 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 244 268 4 3 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 244 268 (accept_3_3 11 244 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  244 268 2 5 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 244 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 244 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 244 268 4 2 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 244 268 (Polychromatic418967fa.accept_13_7_10_8_1_567 7 244 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 244 268 2 3 122 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 268 (accept_3_3 5
  244 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 268 4 1 61 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 244 268
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 244 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 244 268 2 1 122 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 244 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 244 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 268))))))))))))))))))))))))) (allB_succ' 26 243 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 243 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 243 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 243 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 24
  243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 243 268 (accept_3_3 23
  243 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 243 268
  (Polychromatic418967fa.accept_26_22_9_8_1_9109 22 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 243 268 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 243 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 243 268 (accept_3_3 20 243 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 243 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 243 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 243 268 (Polychromatic418967fa.accept_7_4_5_2_1_243
  18 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 243 268 (accept_3_3 17
  243 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 268
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 243 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 243 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 243 268 (accept_3_3 14 243 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 243 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 243 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 243 268
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 12 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 243 268 (accept_3_3 11 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 243 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 243 268 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 243 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 243 268 (accept_3_3 8 243 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 243 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 243 268
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 243 268 (accept_3_3 5 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  243 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 243 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 243 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 243 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 243 268 (accept_3_3 2 243 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 243 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 243 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 243 268)))))))))))))))))))))))))) (allB_succ' 27 242 268
  (Eq.refl Bool.true) (allA_of_3_1 27 242 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 241 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 241 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 241 268 (accept_3_3 26 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 241 268 (Polychromatic418967fa.accept_13_12_7_8_1_1104 25 241 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 268
  (Polychromatic418967fa.accept_16_8_1_12_1_984 24 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 241 268 (accept_3_3 23 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 241 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 241 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 268 (accept_3_3 20 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 241 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 268
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 18 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 241 268 (accept_3_3 17 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 241 268 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 241 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 268 (accept_3_3 14 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 241 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 268 (accept_3_3 11 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 241 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 268 (accept_3_3 8 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 268 (Polychromatic418967fa.accept_19_7_13_2_1_2878 7 241 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 268 (accept_3_3 5 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 268 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 241 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 268 (accept_3_3 2 241 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 241 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 268)))))))))))))))))))))))))))) (allB_succ' 29 240
  268 (Eq.refl Bool.true) (allA_succ_of_gcd 28 240 268 4 7 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 240 268 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 240 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 240 268 2 13 120 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 240 268
  (Polychromatic418967fa.accept_19_6_12_2_1_8379 25 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 240 268 4 6 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 240 268 (accept_3_3 23 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  240 268 2 11 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 240 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 240 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 240 268 4 5 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 240 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 19
  240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 268 2 9 120 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 268 (accept_3_3 17
  240 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 240 268 4 4 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 240 268
  (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 240 268 2 7 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 240 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 240 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 268 4 3 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 268 (accept_3_3 11 240 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 240 268 2 5 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 240 268 (Polychromatic418967fa.accept_19_9_12_2_1_9776
  9 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 240 268 4 2 60 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 240 268
  (Polychromatic418967fa.accept_17_7_2_13_1_5397 7 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 240 268 2 3 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 240 268 (accept_3_3 5 240 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 240 268 4 1 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 240 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 240 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 240 268 2 1 120 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 240 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 1
  240 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 240 268)))))))))))))))))))))))))))))
  (allB_succ' 30 239 268 (Eq.refl Bool.true) (allA_of_3_1 30 239 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 31 238 268 (Eq.refl Bool.true) (allA_succ_of_gcd 30 238 268 2 15 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 238 268 (accept_3_3 29 238 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 238 268 2 14 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 238 268 (Polychromatic418967fa.accept_19_8_10_2_1_5414
  27 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 238 268 2 13 119 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 238 268
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 25 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 238 268 2 12 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 238 268 (accept_3_3 23 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 238 268 2 11 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 238 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 238 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 238 268 2 10 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 238 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 238 268 2 9 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 238 268 (accept_3_3 17 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 238 268 2 8 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 238 268 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 238 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 238 268 2 7 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 238 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 238 268 2 6 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 238 268 (accept_3_3 11 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 238 268 2 5 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 238 268 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 238 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 238 268 2 4 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 238 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 238 268 2 3 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 238 268 (accept_3_3 5 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 238 268 2 2 119 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 238 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 238 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 238 268 2 1 119 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 238 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 238 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 238 268))))))))))))))))))))))))))))))) (allB_succ' 32 237 268 (Eq.refl Bool.true) (allA_succ_of_accept 31
  237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 237 268 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 237 268 (accept_3_3 29 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 237 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 237 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 237 268
  (Polychromatic418967fa.accept_20_7_17_8_1_3452 27 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 237 268 (accept_3_3 26 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 237 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 237 268 (accept_3_3 23 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 237 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 237 268
  (Polychromatic418967fa.accept_22_21_17_4_1_16388 21 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 237 268 (accept_3_3 20 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 237 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 237 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 237 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 237 268 (accept_3_3 17 237 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 237 268
  (Polychromatic418967fa.accept_15_1_12_13_1_944 16 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 237 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 237 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 237 268 (accept_3_3 14 237 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 237 268
  (Polychromatic418967fa.accept_17_12_16_13_1_7951 12 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 237 268 (accept_3_3 11 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 237 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 237 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 237 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 237 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 237 268 (accept_3_3 8 237 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 237 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 237 268 (accept_3_3 5 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  237 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 237 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 237 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 237 268 (accept_3_3 2 237 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 237 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 268)))))))))))))))))))))))))))))))) (allB_succ' 33
  236 268 (Eq.refl Bool.true) (allA_of_3_1 33 236 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 235 268
  (Eq.refl Bool.true) (allA_succ_of_accept 33 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 235 268 (accept_3_3 32 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 235 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 235 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 235 268
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 235 268 (accept_3_3 29 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 235 268 (Polychromatic418967fa.accept_18_10_1_16_1_579 28 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 235 268 (accept_3_3 26 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 235 268 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 235 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 235 268
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 235 268 (accept_3_3 23 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 235 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 235 268 (accept_3_3 20 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 235 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 235 268
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 235 268 (accept_3_3 17 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 235 268 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 235 268 (accept_3_3 14 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 235 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 235 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 235 268 (accept_3_3 11 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 235 268 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 235 268 (accept_3_3 8 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 235 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 235 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 235 268 (accept_3_3 5 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  235 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 235 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 235 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 235 268 (accept_3_3 2 235 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 235 268 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 235 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 235 268)))))))))))))))))))))))))))))))))) (allB_succ' 35
  234 268 (Eq.refl Bool.true) (allA_succ_of_gcd 34 234 268 2 17 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 234 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 234 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 234 268 2 16 117 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 234 268
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 31 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 234 268 2 15 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 234 268 (accept_3_3 29 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 234 268 2 14 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 234 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 234 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 234 268 2 13 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 234 268
  (Polychromatic418967fa.accept_20_5_14_8_1_6391 25 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 234 268 2 12 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 234 268 (accept_3_3 23 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 234 268 2 11 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 234 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 234 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 234 268 2 10 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 234 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 268 2 9 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 234 268 (accept_3_3 17 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 234 268 2 8 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 234 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 234 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 234 268 2 7 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 234 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 234 268 2 6 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 234 268 (accept_3_3 11 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 234 268 2 5 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 234 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 234 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 234 268 2 4 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 234 268
  (Polychromatic418967fa.accept_11_7_3_4_1_729 7 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 234 268 2 3 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 234 268 (accept_3_3 5 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 234 268 2 2 117 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 234 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 234 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 234 268 2 1 117 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 234 268
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 234 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 268))))))))))))))))))))))))))))))))))) (allB_succ' 36 233 268 (Eq.refl Bool.true) (allA_of_3_1 36 233
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 232 268 (Eq.refl Bool.true) (allA_succ_of_gcd 36 232 268 4
  9 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 232
  268 (accept_3_3 35 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 232 268 2 17 116 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 232 268
  (Polychromatic418967fa.accept_16_1_8_12_1_405 33 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 232 268 4 8 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 232 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 232 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 232 268 2 15 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 232 268 (accept_3_3 29 232 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 232 268 4 7 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 232 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 232 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 232 268 2 13 116 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 232 268
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 232 268 4 6 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 232 268 (accept_3_3 23 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  232 268 2 11 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 232 268 (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 232 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 232 268 4 5 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 232 268 (Polychromatic418967fa.accept_11_8_1_4_1_2318
  19 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 232 268 2 9 116 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 232 268
  (accept_3_3 17 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 232 268 4 4 58 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 232 268
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 232 268 2 7 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 232 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 232 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 232 268 4 3 58 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 232 268 (accept_3_3 11 232 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 232 268 2 5 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 232 268 (Polychromatic418967fa.accept_13_9_11_8_1_195 9
  232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 232 268 4 2 58 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 232 268
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 7 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 232 268 2 3 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 232 268 (accept_3_3 5 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 232 268 4 1 58 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 232 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 232 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 232 268 2 1 116 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 232 268 (Polychromatic418967fa.accept_13_1_11_8_1_2562
  1 232 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232
  268))))))))))))))))))))))))))))))))))))) (allB_succ' 38 231 268 (Eq.refl Bool.true) (allA_succ_of_accept 37 231 268
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 231 268 (Polychromatic418967fa.accept_16_4_7_12_1_2734 36 231 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 231 268 (accept_3_3 35 231 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 231 268 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 231 268
  (Polychromatic418967fa.accept_10_3_1_8_1_132 33 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 231 268 (accept_3_3 32 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 231 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 231 268 (accept_3_3 29 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 231 268
  (Polychromatic418967fa.accept_8_3_7_4_1_42 27 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 231 268 (accept_3_3 26 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 231 268 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 231 268 (accept_3_3 23 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 231 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 231 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 231 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 231 268 (accept_3_3 20 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 231 268 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 231 268 (accept_3_3 17 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 231 268 (Polychromatic418967fa.accept_19_16_3_2_1_6964 16 231
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 231 268
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 15 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 231 268 (accept_3_3 14 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 231 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 231 268 (accept_3_3 11 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 231 268
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 231 268 (accept_3_3 8 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 231 268 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 231 268 (accept_3_3 5 231 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 231 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 231 268
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 231 268 (accept_3_3 2 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  231 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 231 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 231 268)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 230 268 (Eq.refl Bool.true)
  (allA_of_3_1 39 230 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 229 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 229 268 (accept_3_3 38 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 229 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 229 268 (Polychromatic418967fa.accept_15_6_4_13_1_403
  36 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 229 268 (accept_3_3 35
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 229 268
  (Polychromatic418967fa.accept_10_4_9_8_1_125 34 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 229 268 (accept_3_3 32 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 229 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 229 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 30
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 268 (accept_3_3 29
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 229 268 (accept_3_3 26 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 229 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 229 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 24
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 268 (accept_3_3 23
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 268
  (Polychromatic418967fa.accept_12_10_1_4_1_392 22 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 229 268 (accept_3_3 20 229 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 229 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 229 268 (Polychromatic418967fa.accept_7_4_5_2_1_243
  18 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 268 (accept_3_3 17
  229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 268
  (Polychromatic418967fa.accept_22_16_9_4_1_10288 16 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 229 268 (accept_3_3 14 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 229 268 (Polychromatic418967fa.accept_11_2_9_4_1_310 13 229 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 229 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 229 268 (accept_3_3 11 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 229 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 229 268 (accept_3_3 8 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 229 268 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 229 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 229 268
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 229 268 (accept_3_3 5 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  229 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 229 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 229 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 229 268 (accept_3_3 2 229 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 229 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 229 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 229 268))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 228 268 (Eq.refl Bool.true) (allA_succ_of_gcd 40 228 268 4 10 57 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 228 268
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 228 268 2 19 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 228 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 228 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 228 268 4 9 57 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 228 268 (accept_3_3 35 228 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 228 268 2 17 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 228 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 33
  228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 228 268 4 8 57 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 228 268
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 228 268 2 15 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 228 268 (accept_3_3 29 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 228 268 4 7 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 228 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 228 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 228 268 2 13 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 228 268 (Polychromatic418967fa.accept_13_12_7_8_1_1104
  25 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 228 268 4 6 57 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 228 268
  (accept_3_3 23 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 228 268 2 11 114 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 228 268
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 228 268 4 5 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 228 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 228 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 268 2 9 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 268 (accept_3_3 17 228 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 228 268 4 4 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 228 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 228 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 228 268 2 7 114 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 228 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 228 268 4 3 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 228 268 (accept_3_3 11 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  228 268 2 5 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 228 268 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 228 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 228 268 4 2 57 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 228 268 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 228 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 228 268 2 3 114 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 228 268 (accept_3_3 5
  228 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 228 268 4 1 57 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 228 268
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 228 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 228 268 2 1 114 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 228 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 228 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 228 268))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 227
  268 (Eq.refl Bool.true) (allA_of_3_1 42 227 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 226 268
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 226 268 2 21 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 226 268 (accept_3_3 41 226 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 226 268 2 20 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 226 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 226 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 226 268 2 19 113 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 226 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 226 268 2 18 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 226 268 (accept_3_3 35 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 226 268 2 17 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 226 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 226 268 2 16 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 226 268
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 226 268 2 15 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 226 268 (accept_3_3 29 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 226 268 2 14 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 226 268 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 226 268 2 13 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 226 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 226 268 2 12 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 226 268 (accept_3_3 23 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 226 268 2 11 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 226 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 226 268 2 10 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 226 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 226 268 2 9 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 226 268 (accept_3_3 17 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 226 268 2 8 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 226 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 226 268 2 7 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 226 268
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 226 268 2 6 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 226 268 (accept_3_3 11 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 226 268 2 5 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 226 268 (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 226 268 2 4 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 226 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 226 268 2 3 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 226 268 (accept_3_3 5 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 226 268 2 2 113 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 226 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 226 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 226 268 2 1 113 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 226 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 226 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 226 268))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 225 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 225 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 225 268 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 225
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 225 268 (accept_3_3 41 225
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 225 268
  (Polychromatic418967fa.accept_16_8_1_12_1_984 40 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 225 268 (Polychromatic418967fa.accept_21_18_15_16_1_2917 39 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 225 268 (accept_3_3 38 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 225 268
  (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 225 268 (accept_3_3 35 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 225 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 225 268 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 225 268 (accept_3_3 32 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 225 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 225 268
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 225 268 (accept_3_3 29 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 225 268 (Polychromatic418967fa.accept_22_6_5_4_1_13342 28 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 225 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 225 268 (accept_3_3 26 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 225 268
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 225 268 (accept_3_3 23 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 225 268 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 225 268 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 225 268 (accept_3_3 20 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 225 268
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 225 268 (accept_3_3 17 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 225 268 (Polychromatic418967fa.accept_24_16_9_4_1_13069 16 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 225 268 (Polychromatic418967fa.accept_18_15_9_16_1_6029 15 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 225 268 (accept_3_3 14 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 225 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 225 268
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 225 268 (accept_3_3 11 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 225 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 225 268 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 225 268 (accept_3_3 8 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 225 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 225 268 (accept_3_3 5 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  225 268 (Polychromatic418967fa.accept_16_4_1_12_1_1792 4 225 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 225 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 225 268 (accept_3_3 2 225 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 225 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 225 268))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 224 268 (Eq.refl Bool.true) (allA_of_3_1 45 224 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 223 268 (Eq.refl Bool.true) (allA_succ_of_accept 45 223 268 (Polychromatic418967fa.accept_6_3_1_4_1_25
  45 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 223 268 (accept_3_3 44
  223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 223 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 223 268 (Polychromatic418967fa.accept_19_4_14_2_1_4117 42 223 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 223 268 (accept_3_3 41 223 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 223 268 (Polychromatic418967fa.accept_11_7_3_4_1_729 40 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 223 268 (accept_3_3 38 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 223 268 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 223 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 268 (accept_3_3 35 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 223 268 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 223 268 (accept_3_3 32 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 223 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 223 268 (Polychromatic418967fa.accept_21_9_13_16_1_2914 30 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 268 (accept_3_3 29 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 223 268 (Polychromatic418967fa.accept_21_7_13_16_1_9068 28 223
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 223 268 (accept_3_3 26 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 223 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 223 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 268 (accept_3_3 23 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 223 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 223 268 (accept_3_3 20 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 223 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 223 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 268 (accept_3_3 17 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 223 268 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 223 268 (accept_3_3 14 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 223 268 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 223 268 (Polychromatic418967fa.accept_19_12_14_2_1_1692 12 223 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 268 (accept_3_3 11 223 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 223 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 10
  223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 223 268 (accept_3_3 8 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  223 268 (Polychromatic418967fa.accept_11_7_3_4_1_729 7 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 223 268 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 268 (accept_3_3 5 223 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 223 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 223 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 223 268 (accept_3_3 2 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  223 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 223 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 223 268)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 222 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 222 268 2 23 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 222 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 222 268 2 22 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 222 268
  (Polychromatic418967fa.accept_22_21_2_4_1_10171 43 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 222 268 2 21 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 222 268 (accept_3_3 41 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 222 268 2 20 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 222 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 222 268 2 19 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 222 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 222 268 2 18 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 222 268 (accept_3_3 35 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 222 268 2 17 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 222 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 222 268 2 16 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 222 268
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 222 268 2 15 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 222 268 (accept_3_3 29 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 222 268 2 14 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 222 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 222 268 2 13 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 222 268
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 268 2 12 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 222 268 (accept_3_3 23 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 222 268 2 11 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 222 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 222 268 2 10 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 222 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 222 268 2 9 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 222 268 (accept_3_3 17 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 222 268 2 8 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 222 268 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 222 268 2 7 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 222 268
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 222 268 2 6 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 222 268 (accept_3_3 11 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 222 268 2 5 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 222 268 (Polychromatic418967fa.accept_11_9_2_4_1_707 9 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 222 268 2 4 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 222 268
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 268 2 3 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 222 268 (accept_3_3 5 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 222 268 2 2 111 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 222 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 222 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 222 268 2 1 111 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 222 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 222 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 222 268))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 221 268 (Eq.refl Bool.true)
  (allA_of_3_1 48 221 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 220 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 48 220 268 4 12 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 220 268 (accept_3_3 47 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 220 268 2 23 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 220 268 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 220 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 220 268 4 11 55 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 220 268
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 220 268 2 21 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 220 268 (accept_3_3 41 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 220 268 4 10 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 220 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 220 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 220 268 2 19 110 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 220 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 220 268 4 9 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 220 268 (accept_3_3 35 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  220 268 2 17 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 220 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 220 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 220 268 4 8 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 220 268 (Polychromatic418967fa.accept_13_5_12_8_1_198
  31 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 220 268 2 15 110 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 220 268
  (accept_3_3 29 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 220 268 4 7 55 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 220 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 220 268 2 13 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 220 268 (Polychromatic418967fa.accept_18_7_4_16_1_2299 25 220 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 220 268 4 6 55 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 220 268 (accept_3_3 23 220 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 220 268 2 11 110 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 220 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 220 268 4 5 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 220 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 220 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 220 268 2 9 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 220 268 (accept_3_3 17 220 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 220 268 4 4 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 220 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 220 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 220 268 2 7 110 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 220 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 220 268 4 3 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 220 268 (accept_3_3 11 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  220 268 2 5 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 220 268 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 220 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 220 268 4 2 55 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 220 268 (Polychromatic418967fa.accept_13_7_12_8_1_199 7 220 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 220 268 2 3 110 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 220 268 (accept_3_3 5
  220 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 220 268 4 1 55 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 220 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 220 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 220 268 2 1 110 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 220 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 220 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 268)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 219 268 (Eq.refl Bool.true) (allA_succ_of_accept 49 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 219 268
  (Polychromatic418967fa.accept_13_9_11_8_1_195 48 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 219 268 (accept_3_3 47 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 219 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 219 268 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 219 268 (accept_3_3 44 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 219 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 219 268 (accept_3_3 41 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 219 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 219 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 219 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 219 268 (accept_3_3 38 219 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 219 268
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 219 268 (accept_3_3 35 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 268 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 219 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 219 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 219 268 (accept_3_3 32 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 219 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 219 268 (accept_3_3 29 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 219 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 219 268 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 219 268 (accept_3_3 26 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 219 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 219 268 (accept_3_3 23 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 219 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 219 268 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 219 268 (accept_3_3 20 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 219 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 219 268 (accept_3_3 17 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 219 268 (Polychromatic418967fa.accept_11_5_10_4_1_1157 16 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 219 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 219 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 219 268 (accept_3_3 14 219 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 219 268
  (Polychromatic418967fa.accept_19_12_10_2_1_12527 12 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 219 268 (accept_3_3 11 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 219 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 219 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 219 268 (Polychromatic418967fa.accept_13_9_11_8_1_195 9 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 219 268 (accept_3_3 8 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 219 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 219 268 (accept_3_3 5 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  219 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 219 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 219 268 (Polychromatic418967fa.accept_13_3_11_8_1_1094 3 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 268 (accept_3_3 2 219 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 219 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  268)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 218 268 (Eq.refl Bool.true) (allA_of_3_1 51 218
  268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 217 268 (Eq.refl Bool.true) (allA_succ_of_accept 51 217
  268 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 217 268 (accept_3_3 50 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 217 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 217 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 217 268 (accept_3_3 47 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 217 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 217 268 (accept_3_3 44 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 217 268 (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 217 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 268 (accept_3_3 41 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 217 268 (accept_3_3 38 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 217 268 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 217 268 (Polychromatic418967fa.accept_15_6_7_13_1_1666 36 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 217 268 (accept_3_3 35 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 217 268 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 217
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 217 268 (accept_3_3 32 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 217 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 217 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 217 268 (accept_3_3 29 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 217 268 (Polychromatic418967fa.accept_18_10_1_16_1_579 28 217 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 217 268 (accept_3_3 26 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 217 268 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 217 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 217 268 (accept_3_3 23 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 217 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 217 268 (accept_3_3 20 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 217 268 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 217 268 (Polychromatic418967fa.accept_11_7_8_4_1_718 18 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 217 268 (accept_3_3 17 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 217 268 (Polychromatic418967fa.accept_13_3_9_8_1_4202 16 217
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 217 268 (accept_3_3 14 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 217 268 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 217 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 217 268 (accept_3_3 11 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 217 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 217 268 (accept_3_3 8 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  217 268 (Polychromatic418967fa.accept_11_7_8_4_1_718 7 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 217 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 268 (accept_3_3 5 217 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 268
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 268 (accept_3_3 2 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 268 (Polychromatic418967fa.accept_11_1_8_4_1_717 1 217 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 268)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 216 268 (Eq.refl
  Bool.true) (allA_succ_of_gcd 52 216 268 4 13 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 216 268 (Polychromatic418967fa.accept_16_3_8_12_1_2736 51 216 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 216 268 2 25 108 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 216 268
  (Polychromatic418967fa.accept_15_4_6_13_1_956 49 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 216 268 4 12 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 216 268 (accept_3_3 47 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 216 268 2 23 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 216 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 216 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 216 268 4 11 54 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 216 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 216 268 2 21 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 216 268 (accept_3_3 41 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 216 268 4 10 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 216 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 216 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 216 268 2 19 108 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 216 268
  (Polychromatic418967fa.accept_15_7_6_13_1_936 37 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 216 268 4 9 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 216 268 (accept_3_3 35 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  216 268 2 17 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 216 268 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 216 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 216 268 4 8 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 216 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 31
  216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 268 2 15 108 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 268
  (accept_3_3 29 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 216 268 4 7 54 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 216 268
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 216 268 2 13 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 216 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 216 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 268 4 6 54 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 268 (accept_3_3 23 216 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 216 268 2 11 108 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 216 268
  (Polychromatic418967fa.accept_16_5_8_12_1_1766 21 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 216 268 4 5 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 216 268 (Polychromatic418967fa.accept_11_8_7_4_1_3011 19 216 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 216 268 2 9 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 216 268 (accept_3_3 17 216 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 216 268 4 4 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 216 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 216 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 216 268 2 7 108 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 216 268
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 216 268 4 3 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 216 268 (accept_3_3 11 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  216 268 2 5 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 216 268 (Polychromatic418967fa.accept_16_9_8_12_1_979 9 216 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 216 268 4 2 54 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 216 268 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 216 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 216 268 2 3 108 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 216 268 (accept_3_3 5
  216 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 216 268 4 1 54 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 216 268
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 216 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 216 268 2 1 108 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 216 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 216 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 268)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 215 268 (Eq.refl Bool.true) (allA_of_3_1 54 215 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 55 214 268 (Eq.refl Bool.true) (allA_succ_of_gcd 54 214 268 2 27 107 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 214 268 (accept_3_3 53 214 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 214 268 2 26 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 214 268 (Polychromatic418967fa.accept_14_9_4_2_1_983
  51 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 214 268 2 25 107 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 214 268
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 214 268 2 24 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 268 (accept_3_3 47 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 214 268 2 23 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 214 268 (Polychromatic418967fa.accept_19_7_5_2_1_2842 45 214 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 214 268 2 22 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 214 268
  (Polychromatic418967fa.accept_11_10_5_4_1_711 43 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 214 268 2 21 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 214 268 (accept_3_3 41 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 214 268 2 20 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 214 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 214 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 214 268 2 19 107 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 214 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 214 268 2 18 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 214 268 (accept_3_3 35 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 214 268 2 17 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 214 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 214 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 214 268 2 16 107 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 214 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 214 268 2 15 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 214 268 (accept_3_3 29 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 214 268 2 14 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 214 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 214 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 214 268 2 13 107 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 214 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 214 268 2 12 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 214 268 (accept_3_3 23 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 214 268 2 11 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 214 268 (Polychromatic418967fa.accept_11_10_5_4_1_711 21 214 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 214 268 2 10 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 214 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 214 268 2 9 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 214 268 (accept_3_3 17 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 214 268 2 8 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 214 268 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 214 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 214 268 2 7 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 214 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 214 268 2 6 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 214 268 (accept_3_3 11 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 214 268 2 5 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 214 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 214 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 214 268 2 4 107 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 214 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 214 268 2 3 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 214 268 (accept_3_3 5 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 268 2 2 107 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 268 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 214 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 268 2 1 107 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 214 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 268))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 213 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 213 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 213 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 213 268 (accept_3_3 53 213 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 213 268
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 213 268 (Polychromatic418967fa.accept_10_1_3_8_1_136 51 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 213 268 (accept_3_3 50 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 213 268 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 213 268 (accept_3_3 47
  213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 213 268 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 213 268 (accept_3_3 44 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 213 268 (Polychromatic418967fa.accept_12_6_9_4_1_96
  42 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 213 268 (accept_3_3 41
  213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 213 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 213 268 (accept_3_3 38 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 213 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 213 268 (accept_3_3 35
  213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 213 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 213 268 (accept_3_3 32 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 213 268 (Polychromatic418967fa.accept_9_3_6_7_1_562
  30 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 213 268 (accept_3_3 29
  213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 213 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 213 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 213 268 (accept_3_3 26 213 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 213 268
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 213 268 (accept_3_3 23 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 213 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 213 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 213 268 (accept_3_3 20 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 213 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 213 268
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 213 268 (accept_3_3 17 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 213 268 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 213 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 213 268 (accept_3_3 14 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 213 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 213 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 213 268 (accept_3_3 11 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 213 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 213 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 268 (accept_3_3 8 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 213 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 213 268 (accept_3_3 5 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  213 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 213 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 213 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 268 (accept_3_3 2 213 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 213 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 212 268 (Eq.refl Bool.true) (allA_of_3_1 57
  212 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 211 268 (Eq.refl Bool.true) (allA_succ_of_accept 57
  211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 211 268 (accept_3_3 56 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 211 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 211 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 211 268 (Polychromatic418967fa.accept_25_4_11_18_1_16387 54
  211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 211 268 (accept_3_3 53
  211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 211 268
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 211 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 211 268 (accept_3_3 50 211 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 211 268 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 268 (accept_3_3 47 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 268 (accept_3_3 44 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 268 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 268
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 268 (accept_3_3 41 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 268 (Polychromatic418967fa.accept_15_10_1_13_1_2609 40 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 268 (accept_3_3 38 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 268
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 268 (accept_3_3 35 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 268 (accept_3_3 32 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 268 (accept_3_3 29 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 268 (accept_3_3 26 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 268 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 211 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 268
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 268 (accept_3_3 23 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 268 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 268 (accept_3_3 20 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 268
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 268 (accept_3_3 17 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 268 (Polychromatic418967fa.accept_23_16_4_15_1_16386 16 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 268 (accept_3_3 14 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 268 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 211 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 268 (accept_3_3 11 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 268 (accept_3_3 8 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 268 (accept_3_3 5 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 268 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 211 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 268 (accept_3_3 2 211 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 211 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 210 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 210 268 2 29 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 210 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 210 268 2 28 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 210 268
  (Polychromatic418967fa.accept_9_1_3_7_1_6 55 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 210 268 2 27 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 210 268 (accept_3_3 53 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 210 268 2 26 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 210 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 210 268 2 25 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 210 268
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 210 268 2 24 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 210 268 (accept_3_3 47 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 210 268 2 23 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 210 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 210 268 2 22 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 210 268
  (Polychromatic418967fa.accept_23_20_3_15_1_16385 43 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 210 268 2 21 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 210 268 (accept_3_3 41 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 210 268 2 20 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 210 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 210 268 2 19 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 210 268
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 210 268 2 18 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 210 268 (accept_3_3 35 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 210 268 2 17 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 210 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 210 268 2 16 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 210 268
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 268 2 15 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 268 (accept_3_3 29 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 210 268 2 14 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 210 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 210 268 2 13 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 210 268
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 25 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 210 268 2 12 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 210 268 (accept_3_3 23 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 210 268 2 11 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 210 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 210 268 2 10 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 210 268
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 268 2 9 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 210 268 (accept_3_3 17 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 210 268 2 8 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 210 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 210 268 2 7 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 210 268
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 210 268 2 6 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 210 268 (accept_3_3 11 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 210 268 2 5 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 210 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 268 2 4 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 268
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 7 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 268 2 3 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 210 268 (accept_3_3 5 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 268 2 2 105 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 210 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 268 2 1 105 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 268
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 209 268 (Eq.refl
  Bool.true) (allA_of_3_1 60 209 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 208 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 208 268 4 15 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 208 268 (accept_3_3 59 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 208 268 2 29 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 208 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 208 268 4 14 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 208 268
  (Polychromatic418967fa.accept_18_1_10_16_1_566 55 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 208 268 2 27 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 208 268 (accept_3_3 53 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 208 268 4 13 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 208 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 208 268 2 25 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 208 268
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 208 268 4 12 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 208 268 (accept_3_3 47 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 208 268 2 23 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 208 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 208 268 4 11 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 208 268
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 43 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 208 268 2 21 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 208 268 (accept_3_3 41 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 208 268 4 10 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 208 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 208 268 2 19 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 208 268
  (Polychromatic418967fa.accept_17_3_4_13_1_2030 37 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 208 268 4 9 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 208 268 (accept_3_3 35 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  208 268 2 17 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 208 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 208 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 208 268 4 8 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 208 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 31
  208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 208 268 2 15 104 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 208 268
  (accept_3_3 29 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 208 268 4 7 52 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 208 268
  (Polychromatic418967fa.accept_11_5_10_4_1_1157 27 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 208 268 2 13 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 208 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 208 268 4 6 52 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 208 268 (accept_3_3 23 208 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 208 268 2 11 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 208 268 (Polychromatic418967fa.accept_9_3_1_7_1_97 21
  208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 208 268 4 5 52 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 208 268
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 208 268 2 9 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 208 268 (accept_3_3 17 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 208 268 4 4 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 208 268 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 208 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 208 268 2 7 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 208 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 13
  208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 208 268 4 3 52 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 268 (accept_3_3 11
  208 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 268 2 5 104 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 268
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 268 4 2 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 208 268 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 208 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 268 2 3 104 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 268 (accept_3_3 5 208 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 268 4 1 52 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 208 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 208 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 268 2 1 104 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 268
  (Polychromatic418967fa.accept_18_1_10_16_1_566 1 208 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 207 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 207 268
  (Polychromatic418967fa.accept_19_3_17_2_1_6963 60 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 207 268 (accept_3_3 59 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 207 268 (Polychromatic418967fa.accept_25_8_7_18_1_16384 58 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 207 268 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 207 268 (accept_3_3 56 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 207 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 207 268 (accept_3_3 53 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 207 268 (Polychromatic418967fa.accept_16_4_15_12_1_1745 52 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 207 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 207 268 (accept_3_3 50 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 207 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 207 268 (accept_3_3 47 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 207 268 (Polychromatic418967fa.accept_11_2_9_4_1_310 46 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 207 268 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 207 268 (accept_3_3 44 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 207 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 207 268 (accept_3_3 41 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 207 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 207 268 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 207 268 (accept_3_3 38 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 207 268
  (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 207 268 (accept_3_3 35 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 207 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 207 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 207 268 (accept_3_3 32 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 207 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 207 268 (accept_3_3 29 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 207 268 (Polychromatic418967fa.accept_19_9_17_2_1_5428 28 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 207 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 207 268 (accept_3_3 26 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 207 268
  (Polychromatic418967fa.accept_11_2_9_4_1_310 24 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 207 268 (accept_3_3 23 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 207 268 (Polychromatic418967fa.accept_13_9_12_8_1_570 22 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 207 268 (Polychromatic418967fa.accept_17_4_3_13_1_6692 21 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 207 268 (accept_3_3 20 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 207 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 207 268 (accept_3_3 17 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 207 268 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 207 268 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 268 (accept_3_3 14 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 207 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 207 268 (accept_3_3 11 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 207 268 (Polychromatic418967fa.accept_13_10_12_8_1_2550 10 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 207 268 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 268 (accept_3_3 8 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 207 268 (accept_3_3 5 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  207 268 (Polychromatic418967fa.accept_13_4_12_8_1_197 4 207 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 207 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 268 (accept_3_3 2 207 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 206 268 (Eq.refl Bool.true)
  (allA_of_3_1 63 206 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 205 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 205 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 205 268 (accept_3_3 62 205 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 205 268 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 205 268
  (Polychromatic418967fa.accept_14_4_9_2_1_95 60 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 205 268 (accept_3_3 59 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 205 268 (Polychromatic418967fa.accept_11_3_7_4_1_1133 58 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 205 268 (accept_3_3 56 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 205 268 (Polychromatic418967fa.accept_18_1_7_16_1_1342 55 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 205 268
  (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 205 268 (accept_3_3 53 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 205 268 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 205 268 (accept_3_3 50 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 205 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 205 268
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 48 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 205 268 (accept_3_3 47 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 205 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 205 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 205 268 (accept_3_3 44 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 205 268 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  43 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 268
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 205 268 (accept_3_3 41 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 205 268 (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 268 (accept_3_3 38 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 205 268 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 268
  (Polychromatic418967fa.accept_11_3_7_4_1_1133 36 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 268 (accept_3_3 35 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 268 (accept_3_3 32 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 268 (Polychromatic418967fa.accept_13_5_10_8_1_1127 31 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 268
  (Polychromatic418967fa.accept_11_8_7_4_1_3011 30 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 268 (accept_3_3 29 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 268 (Polychromatic418967fa.accept_13_2_10_8_1_1126 28 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 268 (accept_3_3 26 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 268
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 205 268 (accept_3_3 23 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 205 268 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 205 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 268 (accept_3_3 20 205 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 268 (Polychromatic418967fa.accept_11_8_7_4_1_3011
  19 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 268
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 268 (accept_3_3 17 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 268 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 268 (accept_3_3 14 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 268 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 268
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 268 (accept_3_3 11 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 268 (accept_3_3 8 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 268 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 268
  (Polychromatic418967fa.accept_19_6_15_2_1_2857 6 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 268 (accept_3_3 5 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 268 (Polychromatic418967fa.accept_13_4_10_8_1_1817 4 205 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 268 (accept_3_3 2 205 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 268 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 205 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 204 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 204 268 4 16 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 204 268 (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 204 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 204 268 2 31 102 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 204 268
  (Polychromatic418967fa.accept_19_4_14_2_1_4117 61 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 204 268 4 15 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 204 268 (accept_3_3 59 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 204 268 2 29 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 204 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 204 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 204 268 4 14 51 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 204 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 268 2 27 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 268 (accept_3_3 53 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 204 268 4 13 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 204 268 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 204 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 204 268 2 25 102 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 204 268
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 268 4 12 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 268 (accept_3_3 47 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 204 268 2 23 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 204 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 204 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 204 268 4 11 51 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 204 268
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 43 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 268 2 21 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 268 (accept_3_3 41 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 204 268 4 10 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 204 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 204 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 204 268 2 19 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 204 268
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 204 268 4 9 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 204 268 (accept_3_3 35 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  204 268 2 17 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 204 268 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 204 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 204 268 4 8 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 204 268 (Polychromatic418967fa.accept_7_3_1_2_1_247 31
  204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 204 268 2 15 102 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 204 268
  (accept_3_3 29 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 204 268 4 7 51 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 204 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 204 268 2 13 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 204 268 (Polychromatic418967fa.accept_13_12_9_8_1_2595 25 204 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 268 4 6 51 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 268 (accept_3_3 23 204 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 204 268 2 11 102 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 204 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 204 268 4 5 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 204 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 204 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 268 2 9 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 268 (accept_3_3 17 204 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 204 268 4 4 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 268 (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 204
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 268 2 7 102 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 268
  (Polychromatic418967fa.accept_7_6_1_2_1_230 13 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 204 268 4 3 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 204 268 (accept_3_3 11 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  204 268 2 5 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 204 268 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 204 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 268 4 2 51 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 268 (Polychromatic418967fa.accept_13_7_9_8_1_188 7 204 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 268 2 3 102 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 268 (accept_3_3 5
  204 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 268 4 1 51 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 268
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 268 2 1 102 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 203 268 (Eq.refl Bool.true)
  (allA_of_3_1 66 203 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 202 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 202 268 2 33 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 202 268 (accept_3_3 65 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 202 268 2 32 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 202 268 (Polychromatic418967fa.accept_19_6_12_2_1_8379 63 202 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 202 268 2 31 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 202 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 202 268 2 30 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 202 268 (accept_3_3 59 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 202 268 2 29 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 202 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 202 268 2 28 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 202 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 202 268 2 27 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 202 268 (accept_3_3 53 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 202 268 2 26 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 202 268 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 202 268 2 25 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 202 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 202 268 2 24 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 202 268 (accept_3_3 47 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 202 268 2 23 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 202 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 202 268 2 22 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 202 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 202 268 2 21 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 202 268 (accept_3_3 41 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 202 268 2 20 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 202 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 202 268 2 19 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 202 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 202 268 2 18 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 202 268 (accept_3_3 35 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 202 268 2 17 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 202 268 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 202 268 2 16 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 202 268
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 202 268 2 15 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 202 268 (accept_3_3 29 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 202 268 2 14 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 202 268 (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 202 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 202 268 2 13 101 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 202 268
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 202 268 2 12 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 202 268 (accept_3_3 23 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 202 268 2 11 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 268 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 202 268 2 10 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 202 268
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 202 268 2 9 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 268 (accept_3_3 17 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 268 2 8 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 268 2 7 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 268
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 268 2 6 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 268 (accept_3_3 11 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 268 2 5 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 268 (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 268 2 4 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 268
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 268 2 3 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 268 (accept_3_3 5 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 268 2 2 101 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 202 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 268 2 1 101 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 202 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 201 268 (Eq.refl
  Bool.true) (allA_succ_of_gcd 67 201 268 67 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 66 201 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 201 268 (accept_3_3 65 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 201 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 201 268
  (Polychromatic418967fa.accept_10_3_1_8_1_132 63 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 201 268 (accept_3_3 62 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 201 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 201 268 (accept_3_3 59 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 201 268
  (Polychromatic418967fa.accept_22_13_3_4_1_10222 57 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 201 268 (accept_3_3 56 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 201 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 201 268 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 201 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 201 268 (accept_3_3 53 201 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 52
  201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 201 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 201 268 (accept_3_3 50 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 201 268 (Polychromatic418967fa.accept_19_10_11_2_1_8354 48 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 201 268 (accept_3_3 47 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 201 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 201 268
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 201 268 (accept_3_3 44 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 201 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 201 268 (accept_3_3 41 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 201 268
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 201 268 (accept_3_3 38 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 201 268 (Polychromatic418967fa.accept_16_4_9_12_1_4829 36 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 201 268 (accept_3_3 35 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 268 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 201
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 201 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 201 268 (accept_3_3 32 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 201 268 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 201 268 (accept_3_3 29 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 201 268 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 201 268
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 201 268 (accept_3_3 26 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 201 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 201 268 (accept_3_3 23 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 268 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 268
  (Polychromatic418967fa.accept_8_5_1_4_1_628 21 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 268 (accept_3_3 20 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 268 (accept_3_3 17 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 268 (Polychromatic418967fa.accept_19_16_11_2_1_12465 16 201 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 268
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 268 (accept_3_3 14 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 268 (Polychromatic418967fa.accept_26_12_19_8_1_11021 12 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 268 (accept_3_3 11 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 268 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 201 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 268
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 268 (accept_3_3 8 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 268 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 268 (accept_3_3 5 201 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 268 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 201 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 268
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 268 (accept_3_3 2 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 200
  268 (Eq.refl Bool.true) (allA_of_3_1 69 200 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 199 268
  (Eq.refl Bool.true) (allA_succ_of_accept 69 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 199 268 (accept_3_3 68 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 199 268 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 199 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 199 268
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 199 268 (accept_3_3 65 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 199 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 199 268 (accept_3_3 62 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 199 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 268
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 268 (accept_3_3 59 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 268 (accept_3_3 56 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 268 (accept_3_3 53 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 268 (Polychromatic418967fa.accept_11_8_1_4_1_2318 52 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 268 (accept_3_3 50 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 268 (accept_3_3 47 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 268 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 268 (accept_3_3 44 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 268
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 268 (accept_3_3 41 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 268 (accept_3_3 38 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 268 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 268
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 268 (accept_3_3 35 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 268 (accept_3_3 32 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 268
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 268 (accept_3_3 29 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 268 (Polychromatic418967fa.accept_17_11_12_13_1_3030 28 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 268 (accept_3_3 26 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 268 (Polychromatic418967fa.accept_13_12_4_8_1_1120 25 199
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 268
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 268 (accept_3_3 23 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 268 (accept_3_3 20 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 268 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 268
  (Polychromatic418967fa.accept_16_2_7_12_1_3793 18 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 268 (accept_3_3 17 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 268 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 268 (accept_3_3 14 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 268 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 199 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 268
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 268 (accept_3_3 11 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 268 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 268 (accept_3_3 8 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 268 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 268
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 268 (accept_3_3 5 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 268 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 199 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 268 (accept_3_3 2 199 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 268 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 199 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 198 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 198 268 2 35 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 198 268 2 34 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 198 268
  (Polychromatic418967fa.accept_19_10_8_2_1_831 67 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 198 268 2 33 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 198 268 (accept_3_3 65 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 198 268 2 32 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 198 268 2 31 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 198 268
  (Polychromatic418967fa.accept_13_9_3_8_1_573 61 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 198 268 2 30 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 198 268 (accept_3_3 59 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 198 268 2 29 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 198 268 2 28 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 198 268
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 55 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 198 268 2 27 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 198 268 (accept_3_3 53 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 198 268 2 26 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 198 268 2 25 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 198 268
  (Polychromatic418967fa.accept_17_15_11_13_1_2039 49 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 198 268 2 24 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 198 268 (accept_3_3 47 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 198 268 2 23 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 198 268 2 22 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 198 268
  (Polychromatic418967fa.accept_19_5_8_2_1_1707 43 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 198 268 2 21 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 198 268 (accept_3_3 41 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 198 268 2 20 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 198 268 2 19 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 198 268
  (Polychromatic418967fa.accept_13_11_3_8_1_1786 37 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 268 2 18 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 198 268 (accept_3_3 35 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 198 268 2 17 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 198 268 2 16 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 198 268
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 31 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 198 268 2 15 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 198 268 (accept_3_3 29 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 198 268 2 14 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 198 268 2 13 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 198 268
  (Polychromatic418967fa.accept_15_10_3_13_1_4480 25 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 198 268 2 12 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 198 268 (accept_3_3 23 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 198 268 2 11 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 198 268 2 10 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 268
  (Polychromatic418967fa.accept_23_19_14_15_1_1859 19 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 198 268 2 9 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 198 268 (accept_3_3 17 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 268 2 8 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 268 2 7 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 268
  (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 268 2 6 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 268 (accept_3_3 11 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 268 2 5 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 268 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 198 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 268 2 4 99 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 268
  (Polychromatic418967fa.accept_13_7_3_8_1_1750 7 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 268 2 3 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 268 (accept_3_3 5 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  268 2 2 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 268 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 198 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 268 2 1 99 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 268 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 198 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 197 268 (Eq.refl Bool.true)
  (allA_of_3_1 72 197 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 196 268 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 196 268 4 18 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 196 268 (accept_3_3 71 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 196 268 2 35 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 196 268 (Polychromatic418967fa.accept_16_5_4_12_1_3800 69 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 196 268 4 17 49 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 196 268
  (Polychromatic418967fa.accept_16_3_4_12_1_3799 67 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 196 268 2 33 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 196 268 (accept_3_3 65 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 196 268 4 16 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 196 268 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 196 268 2 31 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 196 268
  (Polychromatic418967fa.accept_13_9_1_8_1_1742 61 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 196 268 4 15 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 196 268 (accept_3_3 59 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 196 268 2 29 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 196 268 (Polychromatic418967fa.accept_11_2_9_4_1_310 57 196 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 196 268 4 14 49 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 196 268
  (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 196 268 2 27 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 196 268 (accept_3_3 53 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 196 268 4 13 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 196 268 (Polychromatic418967fa.accept_13_12_1_8_1_1779 51 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 196 268 2 25 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 196 268
  (Polychromatic418967fa.accept_16_1_4_12_1_376 49 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 196 268 4 12 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 196 268 (accept_3_3 47 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 196 268 2 23 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 196 268 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 196 268 4 11 49 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 196 268
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 196 268 2 21 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 196 268 (accept_3_3 41 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 196 268 4 10 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 196 268 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 196 268 2 19 98 134 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 196 268
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 37 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 196 268 4 9 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 196 268 (accept_3_3 35 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  196 268 2 17 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 196 268 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 196 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 196 268 4 8 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 196 268 (Polychromatic418967fa.accept_13_5_1_8_1_1115
  31 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 196 268 2 15 98 134
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 196 268
  (accept_3_3 29 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 196 268 4 7 49 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 196 268
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 27 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 196 268 2 13 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 196 268 (Polychromatic418967fa.accept_13_12_1_8_1_1779 25 196 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 196 268 4 6 49 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 268 (accept_3_3 23 196 268
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 268 2 11 98 134 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 268
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 196 268 4 5 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 268 (Polychromatic418967fa.accept_13_6_1_8_1_1116 19 196 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 268 2 9 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 268 (accept_3_3 17 196 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 268 4 4 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 268 (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 196
  268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 268 2 7 98 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 268
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 268 4 3 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 196 268 (accept_3_3 11 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  196 268 2 5 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 196 268 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 196 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 268 4 2 49 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 268 (Polychromatic418967fa.accept_13_7_1_8_1_1778 7 196 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 268 2 3 98 134 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 268 (accept_3_3 5
  196 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 268 4 1 49 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 196 268
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 196 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 196 268 2 1 98 134 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 196 268 (Polychromatic418967fa.accept_16_1_4_12_1_376 1 196 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 196
  268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 195 268 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 195 268 (Polychromatic418967fa.accept_10_2_5_8_1_139
  72 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 195 268 (accept_3_3 71
  195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 195 268
  (Polychromatic418967fa.accept_20_10_15_8_1_4818 70 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 195 268 (Polychromatic418967fa.accept_22_3_19_4_1_13346 69 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 195 268 (accept_3_3 68 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 195 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 195 268
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 195 268 (accept_3_3 65 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 195 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 195 268 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 195 268 (accept_3_3 62 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 195 268
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 195 268 (accept_3_3 59 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 195 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 195 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 195 268 (accept_3_3 56 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 195 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 195 268 (accept_3_3 53 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 195 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 195 268 (Polychromatic418967fa.accept_11_7_8_4_1_718 51 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 195 268 (accept_3_3 50 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 195 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 195 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 195 268 (accept_3_3 47 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 195 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 195 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 195 268 (accept_3_3 44 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 195 268
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 195 268 (accept_3_3 41 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 195 268 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 195 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 195 268 (accept_3_3 38 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 195 268
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 195 268 (accept_3_3 35 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 195 268 (Polychromatic418967fa.accept_11_1_8_4_1_717 34 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 195 268 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 195 268 (accept_3_3 32 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 195 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 195 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 195 268 (accept_3_3 29 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 195 268 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 195 268 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 195 268 (accept_3_3 26 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 195 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 195 268
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 195 268 (accept_3_3 23 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 195 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 195 268 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 268 (accept_3_3 20 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 268
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 268 (accept_3_3 17 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 195 268 (Polychromatic418967fa.accept_19_16_5_2_1_8375 16 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 195 268 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 268 (accept_3_3 14 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 268
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 268 (accept_3_3 11 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 195 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 195 268 (Polychromatic418967fa.accept_16_9_3_12_1_1802 9 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 268 (accept_3_3 8 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 268
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 268 (accept_3_3 5 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 268 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 195 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 268 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 268 (accept_3_3 2 195 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 268 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 195 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  268)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 194 268 (Eq.refl
  Bool.true) (allA_of_3_1 75 194 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 193 268 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 193 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 193 268 (accept_3_3 74 193 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 193 268 (Polychromatic418967fa.accept_16_8_1_12_1_984
  72 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 193 268 (accept_3_3 71
  193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 193 268
  (Polychromatic418967fa.accept_12_10_1_4_1_392 70 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 193 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 193 268 (accept_3_3 68 193 268 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 193 268 (Polychromatic418967fa.accept_27_13_4_25_1_16383 67 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 193 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 193 268 (accept_3_3 65 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 193 268 (accept_3_3 62 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 193 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 193 268
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 193 268 (accept_3_3 59 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 193 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 193 268 (accept_3_3 56 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 193 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 193 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 193 268 (accept_3_3 53 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 193 268 (Polychromatic418967fa.accept_16_4_1_12_1_1792 52 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 193 268 (accept_3_3 50 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 193 268 (Polychromatic418967fa.accept_13_10_11_8_1_1770 49 193 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 193 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 193 268 (accept_3_3 47 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 193 268 (accept_3_3 44 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 193 268 (Polychromatic418967fa.accept_13_4_11_8_1_1768 43 193 268
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 193 268
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 193 268 (accept_3_3 41 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 193 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 193 268 (accept_3_3 38 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 193 268 (Polychromatic418967fa.accept_8_5_1_4_1_628 37 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 193 268
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 193 268 (accept_3_3 35 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 193 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 193 268 (accept_3_3 32 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 193 268 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 193 268
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 193 268 (accept_3_3 29 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 268 (accept_3_3 26 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 268 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 193 268
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 193 268 (accept_3_3 23 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 193 268 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 268 (accept_3_3 20 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 268 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 268
  (Polychromatic418967fa.accept_16_2_1_12_1_3798 18 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 268 (accept_3_3 17 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 268 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 268 (accept_3_3 14 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 268 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 268
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 268 (accept_3_3 11 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 268 (accept_3_3 8 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 268 (Polychromatic418967fa.accept_17_7_6_13_1_10548 7 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 268
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 268 (accept_3_3 5 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 268 (Polychromatic418967fa.accept_13_4_11_8_1_1768 4 193 268 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 268 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 268 (accept_3_3 2 193 268 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 268 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 268 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193
  268))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_268_segment_001)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


