-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch261
-- name    : Polychromatic418967fa_Branch261
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:32:33.054119+00:00
-- url     : https://prove2.me/theorems/febe01e6-8f2b-434e-8f8b-258162f68ac9
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch261_Segment002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_261 : allB 261 261 :=
  allB_succ' 2 260 261 (Eq.refl Bool.true) (allA_succ_of_accept 1 260 261 (accept_3_4 1 260 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 260 261)) (allB_succ' 3 259 261 (Eq.refl Bool.true) (allA_succ_of_accept 2 259 261
  (accept_3_5 2 259 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 261
  (Polychromatic418967fa.accept_25_1_9_11_1_5135 1 259 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 259 261))) (allB_succ' 4 258 261 (Eq.refl Bool.true) (allA_succ_of_gcd 3 258 261 3 1 86 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 258 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 258 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 258 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 258 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 258 261)))) (allB_succ' 5 257 261 (Eq.refl Bool.true) (allA_succ_of_accept 4
  257 261 (accept_3_4 4 257 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 257 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 257 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 257 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 257 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 261 (accept_3_4 1 257 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 257 261))))) (allB_succ' 6 256 261 (Eq.refl Bool.true) (allA_succ_of_accept 5 256 261
  (accept_3_5 5 256 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 256 261
  (Polychromatic418967fa.accept_19_4_9_14_1_1345 4 256 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 256 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 256 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 256 261 (accept_3_5 2 256 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 256 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 256 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 256 261)))))) (allB_succ' 7 255 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 255 261 3 2 85 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 255 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 255 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 255 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 255 261 3 1 85 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 255 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 255 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 255 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 255 261))))))) (allB_succ' 8 254 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 254 261 (accept_3_4 7 254 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  254 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 254 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 254 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 254 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 254 261 (accept_3_4 4 254 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 254 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 254 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 254 261
  (Polychromatic418967fa.accept_19_2_7_14_1_2389 2 254 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 254 261 (accept_3_4 1 254 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  261)))))))) (allB_succ' 9 253 261 (Eq.refl Bool.true) (allA_succ_of_accept 8 253 261 (accept_3_5 8 253 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 253 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 253 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 253 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 253 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 253 261 (accept_3_5 5 253 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  253 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 253 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 253 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 253 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 253 261 (accept_3_5 2 253 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 253 261 (Polychromatic418967fa.accept_16_1_13_5_1_2280 1 253 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 253 261))))))))) (allB_succ' 10 252 261 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 252 261 9 1 28 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 252 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 252 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 252 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327
  7 252 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 252 261 3 2 84 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 252 261
  (Polychromatic418967fa.accept_15_5_12_6_1_639 5 252 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 252 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 252 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 252 261 3 1 84 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 252 261 (Polychromatic418967fa.accept_15_2_12_6_1_3063 2 252 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 252 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 1 252 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 252 261)))))))))) (allB_succ' 11 251 261 (Eq.refl Bool.true) (allA_succ_of_accept 10 251 261 (accept_3_4 10
  251 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 251 261
  (Polychromatic418967fa.accept_15_9_11_6_1_637 9 251 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 251 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 251 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 261 (accept_3_4 7 251 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 251 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 251 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 5
  251 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 251 261 (accept_3_4 4 251
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 251 261 (Polychromatic418967fa.accept_7_3_6_2_1_90
  3 251 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 251 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 251 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 251 261 (accept_3_4 1 251 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 251
  261))))))))))) (allB_succ' 12 250 261 (Eq.refl Bool.true) (allA_succ_of_accept 11 250 261 (accept_3_5 11 250 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 250 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10
  250 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 250 261
  (Polychromatic418967fa.accept_19_9_3_14_1_2400 9 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 250 261 (accept_3_5 8 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  250 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 250 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 6 250 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 250 261 (accept_3_5 5 250 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 250 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 250 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 250 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 250 261 (accept_3_5 2 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  250 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 250 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 250 261)))))))))))) (allB_succ' 13 249 261 (Eq.refl Bool.true) (allA_succ_of_gcd 12 249 261 3 4
  83 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 249 261
  (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 249 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 261 (Polychromatic418967fa.accept_18_10_15_9_1_1054 10 249 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 249 261 3 3 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 249 261 (Polychromatic418967fa.accept_10_8_9_1_1_189 8
  249 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 261
  (Polychromatic418967fa.accept_19_7_2_14_1_3569 7 249 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 249 261 3 2 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 249 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 249 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 249 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 249 261 3 1 83 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 249 261
  (Polychromatic418967fa.accept_10_2_9_1_1_185 2 249 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 261 (Polychromatic418967fa.accept_15_1_9_6_1_1323 1 249 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 249 261))))))))))))) (allB_succ' 14 248 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 248 261 (accept_3_4 13 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 248 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 248 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 248 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 248 261 (accept_3_4 10 248 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 248 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 248 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 248 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 248 261 (accept_3_4 7 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  248 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 248 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 248 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 248 261 (accept_3_4 4 248 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 248 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 248 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 248 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 248 261 (accept_3_4 1 248 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 248
  261)))))))))))))) (allB_succ' 15 247 261 (Eq.refl Bool.true) (allA_succ_of_accept 14 247 261 (accept_3_5 14 247 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 247 261 (Polychromatic418967fa.accept_11_2_5_8_1_470
  13 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 247 261
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 247 261 (accept_3_5 11 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 247 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 247 261 (Polychromatic418967fa.accept_23_9_17_8_1_7801 9 247 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 247 261 (accept_3_5 8 247 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 247 261 (Polychromatic418967fa.accept_21_7_16_9_1_2417 7 247
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 247 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 247 261 (accept_3_5 5 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  247 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 247 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 247 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 247 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 247 261 (accept_3_5 2 247 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 247 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 247 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 247 261))))))))))))))) (allB_succ' 16 246 261 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 246 261 3 5 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 246 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 246 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 246 261 (Polychromatic418967fa.accept_7_6_1_2_1_230
  13 246 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 246 261 3 4 82 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 246 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 246 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 246 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 246 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 246 261 3 3 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 246 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 246 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 246 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 246 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 261 3 2 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 246 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 246 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 246 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 246 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 246 261 3 1 82 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 246 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 246 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 246 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 246 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 246 261)))))))))))))))) (allB_succ' 17 245 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 245 261 (accept_3_4 16 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 245 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 245 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 261 (accept_3_4 13 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 261 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 245 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 11 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 245 261 (accept_3_4 10 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  245 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 245 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 261 (accept_3_4 7 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 245 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 5 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 261 (accept_3_4 4 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 245 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 261 (accept_3_4 1 245 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 261))))))))))))))))) (allB_succ' 18 244 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 244 261 (accept_3_5 17 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 244 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 244 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 244 261 (accept_3_5 14 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 244 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 244 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 244 261
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 12 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 244 261 (accept_3_5 11 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 244 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 244 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 244 261 (accept_3_5 8 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 244 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 244 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 244 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 244 261 (accept_3_5 5 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  244 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 244 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 244 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 244 261 (accept_3_5 2 244 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 244 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 244 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 261)))))))))))))))))) (allB_succ' 19 243 261
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 243 261 9 2 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 243 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 243 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 16 243 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 243 261 3 5 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 243 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 243 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 13 243
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 243 261 3 4 81 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 243 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 243 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 243 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 243 261 9 1 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 243 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 243 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 243 261 3 2 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 243 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 243 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 243 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 261 3 1 81 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 243 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 243 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 261))))))))))))))))))) (allB_succ' 20 242 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 242 261 (accept_3_4 19 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 242 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 242 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 242 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 242 261 (accept_3_4 16 242 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 242 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 242 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 242 261
  (Polychromatic418967fa.accept_27_14_26_18_1_14063 14 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 242 261 (accept_3_4 13 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 242 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 242 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 242 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 242 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 242 261 (accept_3_4 10 242 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 242 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9
  242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 242 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 242 261 (accept_3_4 7 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  242 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 242 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 242 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 242 261 (accept_3_4 4 242 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 242 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 242 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 242 261
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 242 261 (accept_3_4 1 242 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  261)))))))))))))))))))) (allB_succ' 21 241 261 (Eq.refl Bool.true) (allA_succ_of_accept 20 241 261 (accept_3_5 20 241
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 241 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 241 261 (accept_3_5 17 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 241 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 241 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 241 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 261 (accept_3_5 14
  241 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 13 241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 241 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 241 261 (accept_3_5 11 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 241 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 241 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 261 (Polychromatic418967fa.accept_11_9_10_8_1_444
  9 241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 261 (accept_3_5 8
  241 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 261
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 241 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 241 261 (accept_3_5 5 241 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 241 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 241 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 241 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 261 (accept_3_5 2 241
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 261 (Polychromatic418967fa.accept_7_1_3_2_1_13
  1 241 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 261)))))))))))))))))))))
  (allB_succ' 22 240 261 (Eq.refl Bool.true) (allA_succ_of_gcd 21 240 261 3 7 80 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 240 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 20 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 240 261 (Polychromatic418967fa.accept_18_1_6_9_1_2001 19 240 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 240 261 3 6 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 240 261
  (Polychromatic418967fa.accept_19_17_12_14_1_3655 17 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 240 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 240 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 240 261 3 5 80 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 240 261
  (Polychromatic418967fa.accept_18_14_6_9_1_1950 14 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 240 261 (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 240 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 240 261 3 4 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 240 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873
  11 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 240 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 240 261 3 3 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 240 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 240 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 240 261 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 240 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 240 261 3 2 80 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 240 261
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 240 261 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 240 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 240 261 3 1 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 240 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 240 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 240 261
  (Polychromatic418967fa.accept_17_1_2_6_1_818 1 240 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 240 261)))))))))))))))))))))) (allB_succ' 23 239 261 (Eq.refl Bool.true) (allA_succ_of_accept 22 239 261
  (accept_3_4 22 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 239 261
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 239 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 239 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 239 261 (accept_3_4 19 239 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 239 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 239 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 239 261 (Polychromatic418967fa.accept_7_3_1_2_1_247
  17 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 239 261 (accept_3_4 16
  239 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 239 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 239 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 239 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 239 261 (accept_3_4 13 239 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 239 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 239 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 239 261
  (Polychromatic418967fa.accept_33_11_8_30_1_15995 11 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 239 261 (accept_3_4 10 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 239 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 239 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 239 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 239 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 239 261 (accept_3_4 7 239 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 239 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 239 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 239 261 (accept_3_4 4 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  239 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 239 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 239 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 239 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 239 261 (accept_3_4 1 239 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 239 261))))))))))))))))))))))) (allB_succ' 24 238 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 238 261 (accept_3_5 23 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 238 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 238 261 (Polychromatic418967fa.accept_22_21_18_19_1_8151 21 238 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 238 261 (accept_3_5 20 238 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 238 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 238 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 238 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 238 261 (accept_3_5 17 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 238 261 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 238 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 238 261 (accept_3_5 14 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 238 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 238 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 238 261
  (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 238 261 (accept_3_5 11 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 238 261 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 238 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 238 261 (accept_3_5 8 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 238 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 238 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 238 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 238 261 (accept_3_5 5 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  238 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 238 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 238 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 238 261 (accept_3_5 2 238 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 238 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 238 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 238 261)))))))))))))))))))))))) (allB_succ' 25 237 261
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 237 261 3 8 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 237 261 (Polychromatic418967fa.accept_19_4_9_14_1_1345 23 237 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 237 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 22 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 237 261 3 7 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 237 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 237 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 237 261 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 237
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 237 261 3 6 79 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 237 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 237 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 237 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 237 261 3 5 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 237 261 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 237 261
  (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 237 261 3 4 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 237 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 237 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 237 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 237 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 237 261 3 3 79 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 237 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 237 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 237 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 237 261 3 2 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 237 261 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 237 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 237 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 237 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 237 261 3 1 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 237 261 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 237 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 237 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 237 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 237 261))))))))))))))))))))))))) (allB_succ' 26
  236 261 (Eq.refl Bool.true) (allA_succ_of_accept 25 236 261 (accept_3_4 25 236 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 236 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 236 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 236 261 (accept_3_4 22
  236 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 236 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 236 261 (Polychromatic418967fa.accept_15_5_11_6_1_692 20 236 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 236 261 (accept_3_4 19 236 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 236 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 236 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 236 261 (accept_3_4 16
  236 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 236 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 15 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 236 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 14 236 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 236 261 (accept_3_4 13 236 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 236 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 236 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 236 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 236 261 (accept_3_4 10 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  236 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 236 261 (Polychromatic418967fa.accept_16_8_12_5_1_200 8 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 236 261 (accept_3_4 7 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 236 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 236 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 236 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 236 261 (accept_3_4 4 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  236 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 236 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 236 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 236 261 (accept_3_4 1 236 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 236 261)))))))))))))))))))))))))) (allB_succ' 27 235 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 235 261 (accept_3_5 26 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 235 261 (Polychromatic418967fa.accept_16_9_11_5_1_2279 25 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 235 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 235 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 235 261 (accept_3_5 23 235 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 235 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 235 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 235 261
  (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 235 261 (accept_3_5 20 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 235 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 235 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 235 261 (accept_3_5 17 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 235 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 235 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 235 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 235 261 (accept_3_5 14 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 235 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 235 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 235 261 (accept_3_5 11 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 235 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 235 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 235 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 235 261 (accept_3_5 8 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  235 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 235 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 235 261 (accept_3_5 5 235 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 235 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 235 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 235 261
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 235 261 (accept_3_5 2 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  235 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 235 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 235 261))))))))))))))))))))))))))) (allB_succ' 28 234 261 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 234 261 9 3 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 234 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 234 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 234
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 234 261 3 8 78 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 234 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 234 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 234 261 3 7 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 234 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 234 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 234 261 9 2 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 234 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 234 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 234
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 234 261 3 5 78 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 234 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 234 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 234 261 3 4 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 234 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 234 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 234 261 9 1 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 234 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 234 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 234 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 234 261 3 2 78 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 234 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 234 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 234 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 234 261 3 1 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 234 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 234 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 234 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 234 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 234 261)))))))))))))))))))))))))))) (allB_succ' 29 233 261 (Eq.refl Bool.true) (allA_succ_of_accept 28 233
  261 (accept_3_4 28 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 233 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 233 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 233 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 233 261 (accept_3_4 25 233 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 233 261 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 233 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 233 261
  (Polychromatic418967fa.accept_20_3_13_1_1_8886 23 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 233 261 (accept_3_4 22 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 233 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 233 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 233 261 (accept_3_4 19 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 233 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 233 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 233 261
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 233 261 (accept_3_4 16 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 233 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 233 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 233 261 (accept_3_4 13 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 233 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 233 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 233 261
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 233 261 (accept_3_4 10 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 233 261 (Polychromatic418967fa.accept_19_9_5_14_1_7872 9 233 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 233 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 233 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 233 261 (accept_3_4 7 233 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 233 261 (Polychromatic418967fa.accept_19_6_5_14_1_3582
  6 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 233 261
  (Polychromatic418967fa.accept_11_5_2_8_1_866 5 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 233 261 (accept_3_4 4 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  233 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 233 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 233 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 233 261 (accept_3_4 1 233 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 233 261))))))))))))))))))))))))))))) (allB_succ' 30 232 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 29 232 261 29 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 28 232 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 232 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 232 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 232 261 (accept_3_5 26 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 232 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25
  232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 232 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 232 261 (accept_3_5 23 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 232 261 (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 232 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 232 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 232 261 (accept_3_5 20 232 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 232 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 232 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 232 261 (accept_3_5 17 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 232 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 232 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 232 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 232 261 (accept_3_5 14 232 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 232 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 232 261
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 232 261 (accept_3_5 11 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 232 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 232 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 232 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 232 261 (accept_3_5 8 232 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 232 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 232 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 232 261 (accept_3_5 5 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  232 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 232 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 232 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 232 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 232 261 (accept_3_5 2 232 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 232 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 232 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 232 261)))))))))))))))))))))))))))))) (allB_succ' 31 231
  261 (Eq.refl Bool.true) (allA_succ_of_gcd 30 231 261 3 10 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 231 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 231 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 231 261
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 28 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 231 261 3 9 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 231 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 231 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 231
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 231 261 3 8 77 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 231 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 23 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 231 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 231 261 3 7 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 231 261
  (Polychromatic418967fa.accept_22_20_11_19_1_14313 20 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 231 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 231 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 231 261 3 6 77 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 231 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 231 261 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 231 261 3 5 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 231 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 231 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 231 261 3 4 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 231 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 231 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 231 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 231 261 3 3 77 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 231 261
  (Polychromatic418967fa.accept_19_8_3_14_1_3571 8 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 231 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 231 261 3 2 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 231 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 231 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 231 261
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 231 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 231 261 3 1 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 231 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 231 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 231 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 231 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 231 261)))))))))))))))))))))))))))))))
  (allB_succ' 32 230 261 (Eq.refl Bool.true) (allA_succ_of_accept 31 230 261 (accept_3_4 31 230 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 230 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 230 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 230 261 (accept_3_4 28 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 230 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 230 261 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 230 261 (accept_3_4 25 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 230 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 230 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 230 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 230 261 (accept_3_4 22 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 230 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 230 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 230 261 (accept_3_4 19 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 230 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 230 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 230 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 230 261 (accept_3_4 16 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 230 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 230 261 (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 230 261 (accept_3_4 13 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 230 261 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 230
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 230 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 230 261 (accept_3_4 10 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  230 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 230 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 230 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 230 261 (accept_3_4 7 230 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 230 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 230 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 230 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 230 261 (accept_3_4 4 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  230 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 230 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 230 261 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 230 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 230 261 (accept_3_4 1 230 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 230 261)))))))))))))))))))))))))))))))) (allB_succ' 33 229 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 229 261 (accept_3_5 32 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 229 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 229 261 (Polychromatic418967fa.accept_20_10_9_1_1_3076 30 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 229 261 (accept_3_5 29 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 229 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 229 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 229 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 27 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 229 261 (accept_3_5 26 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 229 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 229 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 229 261 (accept_3_5 23 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 229 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 229 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 229 261 (accept_3_5 20 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 229 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 229 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 229 261 (accept_3_5 17 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 229 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 229 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 229 261 (accept_3_5 14 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 229 261 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 229 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 229 261 (accept_3_5 11 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 229 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 229 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 229 261
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 229 261 (accept_3_5 8 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  229 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 229 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 6 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 229 261 (accept_3_5 5 229 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 229 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 229 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 229 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 229 261 (accept_3_5 2 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  229 261 (Polychromatic418967fa.accept_23_1_22_8_1_15994 1 229 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 229 261))))))))))))))))))))))))))))))))) (allB_succ' 34 228 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 228 261 3 11 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 228 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 228 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 228 261 (Polychromatic418967fa.accept_15_1_3_6_1_621
  31 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 228 261 3 10 76 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 228 261
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 228 261 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 228 261 3 9 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 228 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 228 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 228 261 3 8 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 228 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 23 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 228 261 (Polychromatic418967fa.accept_16_6_4_5_1_2272 22 228
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 228 261 3 7 76 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 228 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 228 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 228 261 3 6 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 228 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 17
  228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 228 261
  (Polychromatic418967fa.accept_13_3_7_1_1_334 16 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 228 261 3 5 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 228 261 (Polychromatic418967fa.accept_17_14_7_6_1_11222 14 228 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 228 261 (Polychromatic418967fa.accept_7_6_4_2_1_236
  13 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 228 261 3 4 76 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 228 261
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 228 261 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 228 261 3 3 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 228 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 228 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 228 261
  (Polychromatic418967fa.accept_20_7_8_1_1_5856 7 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 228 261 3 2 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 228 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 228 261 (Polychromatic418967fa.accept_18_4_12_9_1_2011 4 228
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 228 261 3 1 76 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 228 261
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 228 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 228 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 228 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 228 261)))))))))))))))))))))))))))))))))) (allB_succ' 35 227 261 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 227 261 (accept_3_4 34 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 227 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 227 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 227 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 227 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 227 261 (accept_3_4 31 227 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 227 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 227 261 (accept_3_4 28 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 227 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 227 261 (accept_3_4 25 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 227 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 227 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 227 261
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 227 261 (accept_3_4 22 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 227 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 227 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 227 261 (accept_3_4 19 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 227 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 227 261
  (Polychromatic418967fa.accept_22_17_7_19_1_11358 17 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 227 261 (accept_3_4 16 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 227 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 227 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 227 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 227 261 (accept_3_4 13 227 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 227 261 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 227 261
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 11 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 227 261 (accept_3_4 10 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  227 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 227 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 227 261 (accept_3_4 7 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 227 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 227 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 227 261 (accept_3_4 4 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  227 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 227 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 227 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 227 261 (accept_3_4 1 227 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 227 261))))))))))))))))))))))))))))))))))) (allB_succ' 36 226 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 226 261 (accept_3_5 35 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 226 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 226 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 226 261 (accept_3_5 32 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 226 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 226 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 226 261 (accept_3_5 29 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 226 261 (Polychromatic418967fa.accept_17_11_5_6_1_4928 28 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 226 261 (accept_3_5 26 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 226 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 226 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 226 261 (accept_3_5 23 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 226 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 226 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 226 261 (accept_3_5 20 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 226 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 226 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 226 261 (accept_3_5 17 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 226 261 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 226 261 (accept_3_5 14 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 226 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 226 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 226 261 (accept_3_5 11 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 226 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 226 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 226 261 (accept_3_5 8 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 226 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 6 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 226 261 (accept_3_5 5 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  226 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 226 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 226 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 226 261 (accept_3_5 2 226 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 226 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 226 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 226 261)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 225 261 (Eq.refl Bool.true) (allA_succ_of_gcd 36 225 261 9 4 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 225 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 225 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 225 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 225 261 3 11 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 225 261 (Polychromatic418967fa.accept_19_13_16_14_1_3517 32 225 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 225 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 225 261 3 10 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 225 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 225 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 225 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 28 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 225 261 9 3 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 225 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 26 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 225 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 225
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 225 261 3 8 75 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 225 261
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 225 261 (Polychromatic418967fa.accept_14_8_1_9_1_2085 22 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 225 261 3 7 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 225 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 20
  225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 225 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 225 261 9 2 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 225 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 225 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 225
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 225 261 3 5 75 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 225 261
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 225 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 225 261 3 4 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 225 261 (Polychromatic418967fa.accept_17_11_4_6_1_2631
  11 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 225 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 225 261 9 1 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 225 261 (Polychromatic418967fa.accept_14_8_1_9_1_2085 8 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 225 261 (Polychromatic418967fa.accept_21_7_15_9_1_5289 7 225
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 225 261 3 2 75 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 225 261
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 225 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 225 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 225 261 3 1 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 225 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 225 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 225 261
  (Polychromatic418967fa.accept_27_1_9_18_1_15993 1 225 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 225 261))))))))))))))))))))))))))))))))))))) (allB_succ' 38 224 261 (Eq.refl Bool.true) (allA_succ_of_accept
  37 224 261 (accept_3_4 37 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 224 261
  (Polychromatic418967fa.accept_19_17_15_14_1_3623 36 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 224 261 (accept_3_4 34 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 224 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 224 261
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 224 261 (accept_3_4 31 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 224 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 224 261 (accept_3_4 28 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 224 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 224 261
  (Polychromatic418967fa.accept_17_9_3_6_1_11232 26 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 224 261 (accept_3_4 25 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 224 261 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 224 261 (accept_3_4 22 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 224 261 (Polychromatic418967fa.accept_18_3_8_9_1_1956 21 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 224 261
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 224 261 (accept_3_4 19 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 224 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 224 261 (accept_3_4 16 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 224 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 224 261
  (Polychromatic418967fa.accept_17_14_3_6_1_3716 14 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 224 261 (accept_3_4 13 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 224 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 224 261 (accept_3_4 10 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 224 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 224 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 224 261 (accept_3_4 7 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  224 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 6 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 224 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 224 261 (accept_3_4 4 224 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 224 261 (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 224 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 224 261
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 224 261 (accept_3_4 1 224 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 224
  261)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 223 261 (Eq.refl Bool.true) (allA_succ_of_accept 38 223 261
  (accept_3_5 38 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 223 261
  (Polychromatic418967fa.accept_15_7_13_6_1_696 37 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 223 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 223 261 (accept_3_5 35 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 223 261 (Polychromatic418967fa.accept_16_1_15_5_1_708
  33 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 223 261 (accept_3_5 32
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 223 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 223 261 (accept_3_5 29 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 223 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 223 261 (Polychromatic418967fa.accept_11_5_3_8_1_454
  27 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 223 261 (accept_3_5 26
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 223 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 223 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 223 261 (accept_3_5 23 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 223 261 (Polychromatic418967fa.accept_17_4_2_6_1_2629
  21 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 223 261 (accept_3_5 20
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 223 261
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 223 261 (accept_3_5 17 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 223 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 223 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 223 261 (accept_3_5 14
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 223 261
  (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 223 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 223 261 (accept_3_5 11 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 223 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 9
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 223 261 (accept_3_5 8 223
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 223 261
  (Polychromatic418967fa.accept_15_7_13_6_1_696 7 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 223 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 223 261 (accept_3_5 5 223 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 223 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 223 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 223 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 223 261 (accept_3_5 2 223
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 223 261 (Polychromatic418967fa.accept_7_1_6_2_1_18
  1 223 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 223
  261))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 222 261 (Eq.refl Bool.true) (allA_succ_of_gcd 39 222 261 3
  13 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 222
  261 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 222 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 37 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 222 261 3 12 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 222 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35
  222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 222 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 34 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 222 261 3 11 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 222 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 222 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 222 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 222 261 3 10 74 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 222 261
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 222 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 28 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 222 261 3 9 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 222 261 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 222 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 222 261 3 8 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 222 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 222 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 222
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 222 261 3 7 74 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 222 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 20 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 222 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 222 261 3 6 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 222 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 222 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 222 261 3 5 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 222 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 14 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 222 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 222
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 222 261 3 4 74 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 222 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 222 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 222 261 3 3 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 222 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 222 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 222 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 222 261 3 2 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 222 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 222 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 222 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 222 261 3 1 74 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 222 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 222 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 222 261 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 222 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 222 261)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 221 261
  (Eq.refl Bool.true) (allA_succ_of_accept 40 221 261 (accept_3_4 40 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 221 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 221 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 221 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 221 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 221 261 (accept_3_4 37 221 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 221 261
  (Polychromatic418967fa.accept_19_17_12_14_1_3655 36 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 221 261 (Polychromatic418967fa.accept_15_5_11_6_1_692 35 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 221 261 (accept_3_4 34 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 221 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 221 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 221 261 (accept_3_4 31 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 221 261 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 221 261 (Polychromatic418967fa.accept_19_10_12_14_1_3613 29 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 221 261 (accept_3_4 28 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 221 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 221 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 221 261 (accept_3_4 25 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 221 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 221 261 (Polychromatic418967fa.accept_21_2_11_9_1_2534 23 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 221 261 (accept_3_4 22 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 221 261 (Polychromatic418967fa.accept_19_2_12_14_1_11919 21
  221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 221 261 (accept_3_4 19 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 221 261 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 221 261 (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 221 261 (accept_3_4 16 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 221 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 221
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 221 261 (accept_3_4 13 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 221 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 221 261 (Polychromatic418967fa.accept_22_11_1_19_1_14315 11 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 221 261 (accept_3_4 10 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 221 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 221 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 221 261 (accept_3_4 7 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  221 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 221 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 221 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 221 261 (accept_3_4 4 221 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 221 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 221 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 221 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 221 261 (accept_3_4 1 221 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 221
  261))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 220 261 (Eq.refl Bool.true) (allA_succ_of_accept 41 220
  261 (accept_3_5 41 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 220 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 220 261 (Polychromatic418967fa.accept_16_7_12_5_1_734 39 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 220 261 (accept_3_5 38 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 220 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36
  220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 220 261 (accept_3_5 35
  220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 220 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 220 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 220 261 (accept_3_5 32 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 220 261 (Polychromatic418967fa.accept_12_6_4_9_1_544
  30 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 220 261 (accept_3_5 29
  220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 220 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 28 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 220 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 220 261 (accept_3_5 26 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 220 261
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 220 261 (accept_3_5 23 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 220 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 220 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 220
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 220 261 (accept_3_5 20 220
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 220 261
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 220 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 18 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 220 261 (accept_3_5 17 220 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 220 261 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 220 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 220 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 220 261 (accept_3_5 14 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 220 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 220 261 (accept_3_5 11 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 220 261 (Polychromatic418967fa.accept_16_10_12_5_1_2254 10 220 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 220 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 220 261 (accept_3_5 8 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 220 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 220 261 (accept_3_5 5 220 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 220 261 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 220 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 220 261
  (Polychromatic418967fa.accept_15_3_10_6_1_632 3 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 220 261 (accept_3_5 2 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  220 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 220 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 220 261)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 219 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 219 261 3 14 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 219 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 41 219 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 219 261
  (Polychromatic418967fa.accept_16_8_11_5_1_3319 40 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 219 261 3 13 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 219 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 219 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 219 261 (Polychromatic418967fa.accept_12_1_3_9_1_174
  37 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 219 261 3 12 73 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 219 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 219 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 219 261 3 11 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 219 261 (Polychromatic418967fa.accept_10_2_9_1_1_185
  32 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 219 261
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 219 261 3 10 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 219 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 219 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 219 261 (Polychromatic418967fa.accept_10_8_9_1_1_189
  28 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 219 261 3 9 73 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 219 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 219 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 219 261 3 8 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 219 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 219 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 219 261 3 7 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 219 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 219 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 19 219
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 219 261 3 6 73 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 219 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 219 261 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 219 261 3 5 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 219 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 219 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 219 261 3 4 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 219 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 219 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 219 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 219 261 3 3 73 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 219 261
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 219 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 219 261 3 2 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 219 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 219 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 219 261
  (Polychromatic418967fa.accept_15_4_9_6_1_627 4 219 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 219 261 3 1 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 219 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 219 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219
  261))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 218 261 (Eq.refl Bool.true) (allA_succ_of_accept 43 218
  261 (accept_3_4 43 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 218 261
  (Polychromatic418967fa.accept_12_6_2_9_1_537 42 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 218 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 218 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 218 261 (accept_3_4 40 218 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 218 261 (Polychromatic418967fa.accept_7_3_1_2_1_247
  38 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 218 261 (accept_3_4 37
  218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 218 261
  (Polychromatic418967fa.accept_19_17_9_14_1_10623 36 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 218 261 (accept_3_4 34 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 218 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 218 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 218 261 (accept_3_4 31 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 218 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 218 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 218 261 (accept_3_4 28 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 218 261
  (Polychromatic418967fa.accept_23_3_11_8_1_15992 26 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 218 261 (accept_3_4 25 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 218 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 218 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 218 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 218 261 (accept_3_4 22 218 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 218 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 218 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 218 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 218 261 (accept_3_4 19 218 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 218 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 218 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 218 261 (accept_3_4 16 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 218 261 (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 218 261 (accept_3_4 13 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 218 261 (Polychromatic418967fa.accept_16_12_10_5_1_5457 12 218
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 218 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 218 261 (accept_3_4 10 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  218 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 218 261 (Polychromatic418967fa.accept_17_8_14_6_1_8727 8 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 218 261 (accept_3_4 7 218 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 218 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 218 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 218 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 218 261 (accept_3_4 4 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  218 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 218 261 (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 261 (accept_3_4 1 218 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 218 261)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 217 261 (Eq.refl
  Bool.true) (allA_succ_of_accept 44 217 261 (accept_3_5 44 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 217 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 43 217 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 217 261 (Polychromatic418967fa.accept_15_12_7_6_1_4013 42 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 217 261 (accept_3_5 41 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 217 261
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 217 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 39 217 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 217 261 (accept_3_5 38 217 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 217 261 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 217 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 36 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 217 261 (accept_3_5 35 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 217 261 (Polychromatic418967fa.accept_14_5_7_9_1_3828 33 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 217 261 (accept_3_5 32 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 217 261 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 217 261
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 217 261 (accept_3_5 29 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 217 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 217 261 (accept_3_5 26 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 217 261 (Polychromatic418967fa.accept_19_6_8_14_1_2351 25 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 217 261
  (Polychromatic418967fa.accept_10_4_7_1_1_471 24 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 217 261 (accept_3_5 23 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 217 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 217 261 (accept_3_5 20 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 217 261 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 217 261
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 217 261 (accept_3_5 17 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 217 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 15 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 217 261 (accept_3_5 14 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 217 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 217
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 217 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 217 261 (accept_3_5 11 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 217 261 (Polychromatic418967fa.accept_19_9_8_14_1_10621 9 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 217 261 (accept_3_5 8 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 217 261 (Polychromatic418967fa.accept_17_7_13_6_1_811 7 217 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 217 261
  (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 217 261 (accept_3_5 5 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  217 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 217 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 217 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 217 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 261 (accept_3_5 2 217 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 261 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 217 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 261)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 216 261 (Eq.refl Bool.true) (allA_succ_of_gcd 45 216 261 9 5 24 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 216 261
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 216 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 216 261 3 14 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 216 261 (Polychromatic418967fa.accept_19_3_7_14_1_3669
  41 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 216 261
  (Polychromatic418967fa.accept_19_2_7_14_1_2389 40 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 216 261 3 13 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 216 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 216 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 216 261 (Polychromatic418967fa.accept_10_7_6_1_1_486
  37 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 216 261 9 4 24 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 216 261
  (Polychromatic418967fa.accept_10_5_6_1_1_836 35 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 216 261 (Polychromatic418967fa.accept_19_15_7_14_1_11879 34 216 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 216 261 3 11 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 216 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 216 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 216 261 3 10 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 216 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 216 261
  (Polychromatic418967fa.accept_16_12_8_5_1_3316 28 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 216 261 9 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 216 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 216 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 216 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 216 261 3 8 72 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 216 261
  (Polychromatic418967fa.accept_19_4_7_14_1_3537 23 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 216 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 216 261 3 7 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 216 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145
  20 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 216 261
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 216 261 9 2 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 216 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 216 261 (Polychromatic418967fa.accept_21_16_6_9_1_8464 16 216
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 216 261 3 5 72 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 216 261
  (Polychromatic418967fa.accept_21_14_6_9_1_14343 14 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 216 261 (Polychromatic418967fa.accept_16_13_8_5_1_3298 13 216 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 216 261 3 4 72 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 216 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 216 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 216 261 9 1 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 216 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 216 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 216 261
  (Polychromatic418967fa.accept_10_7_6_1_1_486 7 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 216 261 3 2 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 216 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 216 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 216 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 216 261 3 1 72 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 216 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 216 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 216 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 216 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 216 261)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 215 261
  (Eq.refl Bool.true) (allA_succ_of_accept 46 215 261 (accept_3_4 46 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 215 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 215 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 215 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 215 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 215 261 (accept_3_4 43 215 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42
  215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 215 261
  (Polychromatic418967fa.accept_15_11_5_6_1_669 41 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 215 261 (accept_3_4 40 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 215 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 215 261 (accept_3_4 37 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 215 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 215 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 215 261
  (Polychromatic418967fa.accept_14_7_5_9_1_2911 35 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 215 261 (accept_3_4 34 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 215 261 (Polychromatic418967fa.accept_15_3_5_6_1_4005 33 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 215 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 215 261 (accept_3_4 31 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 215 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 215 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 215 261 (accept_3_4 28 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 215 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 215 261 (accept_3_4 25 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 215 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 215 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 215 261
  (Polychromatic418967fa.accept_36_23_35_9_1_10877 23 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 215 261 (accept_3_4 22 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 215 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 215 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 215 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 215 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 215 261 (accept_3_4 19 215 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 215 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 17 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 215 261 (accept_3_4 16 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 215 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 215 261 (accept_3_4 13 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 215 261 (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 215 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 215 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 215 261 (accept_3_4 10 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  215 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 215 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 215 261 (accept_3_4 7 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 261
  (Polychromatic418967fa.accept_17_5_11_6_1_4815 5 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 215 261 (accept_3_4 4 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  215 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 215 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 215 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 261 (accept_3_4 1 215 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 215 261))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 214 261 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 214 261 (accept_3_5 47 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 214 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 214 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 214
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 214 261 (accept_3_5 44 214
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 214 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 214 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 42 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 214 261 (accept_3_5 41 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 214 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 214 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 214 261 (accept_3_5 38
  214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 214 261
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 214 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 214 261 (accept_3_5 35 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 214 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 214 261 (Polychromatic418967fa.accept_7_5_4_2_1_235
  33 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 214 261 (accept_3_5 32
  214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 214 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 214 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 30 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 214 261 (accept_3_5 29 214 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 214 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 214 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 214 261 (accept_3_5 26 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 214 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 214 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 214 261 (accept_3_5 23 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 214 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 214
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 214 261
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 214 261 (accept_3_5 20 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 214 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 214 261 (Polychromatic418967fa.accept_12_6_10_9_1_531 18 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 214 261 (accept_3_5 17 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 214 261 (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 214
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 214 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 214 261 (accept_3_5 14 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 214 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 214 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 214 261 (accept_3_5 11 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 214 261 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 214 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 214 261
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 261 (accept_3_5 8 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 261 (accept_3_5 5 214 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 261 (Polychromatic418967fa.accept_16_4_6_5_1_2245 4 214 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 261 (accept_3_5 2 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 214 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 261)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 213 261 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 213 261 3 16 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 213 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 213 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 213 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 46 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 213 261 3 15 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 213 261 (Polychromatic418967fa.accept_21_2_3_9_1_1317 44 213 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 213 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 213 261 3 14 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 213 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 213 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 213 261 (Polychromatic418967fa.accept_7_5_3_2_1_249
  40 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 213 261 3 13 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 213 261
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 213 261 (Polychromatic418967fa.accept_17_3_9_6_1_3726 37 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 213 261 3 12 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 213 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382
  35 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 213 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 34 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 213 261 3 11 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 213 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 213 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 213 261 (Polychromatic418967fa.accept_15_1_3_6_1_621
  31 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 213 261 3 10 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 213 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 213 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 213 261 3 9 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 213 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 26
  213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 213 261
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 213 261 3 8 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 213 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 213 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 213 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 213 261 3 7 71 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 213 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 213 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 213 261 3 6 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 213 261 (Polychromatic418967fa.accept_13_4_5_1_1_833
  17 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 213 261
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 213 261 3 5 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 213 261 (Polychromatic418967fa.accept_20_14_13_1_1_8844 14 213 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 213 261 (Polychromatic418967fa.accept_7_6_3_2_1_461
  13 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 213 261 3 4 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 213 261
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 213 261 (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 213 261 3 3 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 213 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 213 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 213 261 3 2 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 213 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 213 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 213 261 3 1 71 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 213 261
  (Polychromatic418967fa.accept_10_2_3_1_1_481 2 213 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 213 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 213 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 213 261))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 212
  261 (Eq.refl Bool.true) (allA_succ_of_accept 49 212 261 (accept_3_4 49 212 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 212 261 (Polychromatic418967fa.accept_17_14_8_6_1_2643 48 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 212 261 (accept_3_4 46 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 212 261 (Polychromatic418967fa.accept_19_7_3_14_1_5023 45 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 212 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 212 261 (accept_3_4 43 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 212 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 212 261 (accept_3_4 40 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 212 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 39 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 212 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 38 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 212 261 (accept_3_4 37 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 212 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 212 261 (accept_3_4 34 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 212 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 212 261 (Polychromatic418967fa.accept_14_4_2_9_1_2092 32 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 212 261 (accept_3_4 31 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 212 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 212 261 (accept_3_4 28 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 212 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 212 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 26 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 212 261 (accept_3_4 25 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 212 261 (Polychromatic418967fa.accept_16_8_4_5_1_4379 24 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 212 261 (accept_3_4 22 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 212 261 (Polychromatic418967fa.accept_14_7_2_9_1_2093 21 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 212 261 (Polychromatic418967fa.accept_21_20_2_9_1_5337 20 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 212 261 (accept_3_4 19 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 212 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 212 261 (accept_3_4 16 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 212 261 (Polychromatic418967fa.accept_16_15_4_5_1_1411 15 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 212 261 (Polychromatic418967fa.accept_17_14_8_6_1_2643 14 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 212 261 (accept_3_4 13 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 212 261 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 212
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 212 261 (accept_3_4 10 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  212 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 212 261 (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 212 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 261 (accept_3_4 7 212 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 212 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 212 261 (accept_3_4 4 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  212 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 212 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 212 261 (Polychromatic418967fa.accept_22_2_14_19_1_11310 2 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 261 (accept_3_4 1 212 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 212 261)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 211
  261 (Eq.refl Bool.true) (allA_succ_of_accept 50 211 261 (accept_3_5 50 211 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 211 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 211 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 211 261 (accept_3_5 47 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 211 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 211 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 211 261 (accept_3_5 44 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 211 261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 211 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 211 261 (accept_3_5 41 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 211 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 211 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 211 261 (accept_3_5 38 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 211 261 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 211
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 211 261
  (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 211 261 (accept_3_5 35 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 211 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 211 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 211 261 (accept_3_5 32 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 211 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 211 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 211 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 211 261 (accept_3_5 29 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 211 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 211 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 211 261 (accept_3_5 26 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 211 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 25 211 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 211 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 211 261 (accept_3_5 23 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 211 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 211 261 (Polychromatic418967fa.accept_18_3_13_9_1_4260 21 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 211 261 (accept_3_5 20 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 211 261 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 211
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 211 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 211 261 (accept_3_5 17 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 211 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 211 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 15 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 211 261 (accept_3_5 14 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 211 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 211 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 211 261
  (Polychromatic418967fa.accept_19_12_2_14_1_10618 12 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 211 261 (accept_3_5 11 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 211 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 211 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 211 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 9 211 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 261 (accept_3_5 8 211 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 261 (Polychromatic418967fa.accept_13_7_3_1_1_814 7
  211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 261 (accept_3_5 5 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 211 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 261 (accept_3_5 2 211 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 261 (Polychromatic418967fa.accept_19_1_2_14_1_3666 1 211 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211
  261))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 210 261 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  210 261 3 17 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 210 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 50 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 210 261 (Polychromatic418967fa.accept_20_9_10_1_1_192 49 210
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 210 261 3 16 70 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 210 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 46 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 210 261 3 15 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 210 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  44 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 210 261 3 14 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 210 261 (Polychromatic418967fa.accept_18_5_12_9_1_6871 41 210 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 210 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 40 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 210 261 3 13 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 210 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 38 210 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 210 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  37 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 210 261 3 12 70 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 210 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 210 261 3 11 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 210 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  32 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 210 261 3 10 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 210 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 210 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 210 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 210 261 3 9 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 210 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 26 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 210 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 210
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 210 261 3 8 70 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 210 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 210 261 3 7 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 210 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 210 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 210 261 3 6 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 210 261 (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 210 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 210 261 (Polychromatic418967fa.accept_12_4_6_9_1_548
  16 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 210 261 3 5 70 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 210 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 210 261 (Polychromatic418967fa.accept_16_13_2_5_1_3336 13 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 210 261 3 4 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 210 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 210 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 210 261 3 3 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 210 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 210 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 261 3 2 70 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 261
  (Polychromatic418967fa.accept_18_5_12_9_1_6871 5 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 210 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 210 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 210 261 3 1 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 210 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 210 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 261
  (Polychromatic418967fa.accept_22_1_12_19_1_15991 1 210 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 261)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 209 261 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 209 261 (accept_3_4 52 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 209 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 209 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 209 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 209 261 (accept_3_4 49 209 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 209 261 (Polychromatic418967fa.accept_10_8_9_1_1_189
  48 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 209 261
  (Polychromatic418967fa.accept_16_15_1_5_1_2265 47 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 209 261 (accept_3_4 46 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 209 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 209 261 (accept_3_4 43 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 209 261 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 209 261
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 41 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 209 261 (accept_3_4 40 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 209 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 209 261 (accept_3_4 37 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 209 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 209 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 35 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 209 261 (accept_3_4 34 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 209 261 (Polychromatic418967fa.accept_18_15_11_9_1_4256 33 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 209 261 (accept_3_4 31 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 209 261 (Polychromatic418967fa.accept_18_12_11_9_1_4257 30 209 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 209 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 209 261 (accept_3_4 28 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 209 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 27 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 209 261 (accept_3_4 25 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 209 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 209 261
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 209 261 (accept_3_4 22 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 209 261 (Polychromatic418967fa.accept_17_4_5_6_1_8717 21 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 209 261 (accept_3_4 19 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 209 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 209 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 209 261 (accept_3_4 16 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 209 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 209 261 (accept_3_4 13 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 209 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 209 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 209 261 (accept_3_4 10 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  209 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004 9 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 261 (accept_3_4 7 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 261 (Polychromatic418967fa.accept_16_6_1_5_1_2242 6 209 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 261
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 261 (accept_3_4 4 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 209 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 261 (accept_3_4 1 209 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 261))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 208 261
  (Eq.refl Bool.true) (allA_succ_of_accept 53 208 261 (accept_3_5 53 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 208 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 208 261 (Polychromatic418967fa.accept_18_15_10_9_1_2009 51 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 208 261 (accept_3_5 50 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 208 261
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 208 261 (Polychromatic418967fa.accept_18_12_10_9_1_5497 48 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 208 261 (accept_3_5 47 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 208 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 208 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 208 261 (accept_3_5 44 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 208 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 208 261 (accept_3_5 41 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 208 261 (Polychromatic418967fa.accept_27_13_19_18_1_10368 40
  208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 208 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 208 261 (accept_3_5 38 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 208 261 (Polychromatic418967fa.accept_17_2_4_6_1_1619 36 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 208 261 (accept_3_5 35 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 208 261 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 208 261
  (Polychromatic418967fa.accept_10_3_8_1_1_182 33 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 208 261 (accept_3_5 32 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 208 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 30 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 208 261 (accept_3_5 29 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 208 261 (Polychromatic418967fa.accept_17_11_4_6_1_2631 28 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 208 261
  (Polychromatic418967fa.accept_17_10_4_6_1_3757 27 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 208 261 (accept_3_5 26 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 208 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 208 261 (accept_3_5 23 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 208 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 22 208 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 208 261
  (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 208 261 (accept_3_5 20 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 208 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 208 261 (accept_3_5 17 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 208 261 (Polychromatic418967fa.accept_19_16_18_14_1_3562 16 208 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 208 261
  (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 208 261 (accept_3_5 14 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 261 (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 208 261 (accept_3_5 11 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 208 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 10 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 208 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 261 (accept_3_5 8 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 261 (Polychromatic418967fa.accept_12_6_4_9_1_544 6
  208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 208 261 (accept_3_5 5 208
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 208 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 208 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 208 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 261 (accept_3_5 2 208 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 208 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 208 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 261))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 207 261 (Eq.refl Bool.true) (allA_succ_of_gcd 54 207 261 9 6 23 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 207 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 53 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 207 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 207 261 3 17 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 207 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 49 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 207 261 3 16 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 207 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 207 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 207 261 9 5 23 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 207 261
  (Polychromatic418967fa.accept_10_4_7_1_1_471 44 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 207 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 207 261 3 14 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 207 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 41
  207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 207 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 40 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 207 261 3 13 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 207 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 207 261 (Polychromatic418967fa.accept_12_1_3_9_1_174
  37 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 207 261 9 4 23 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 207 261
  (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 207 261 3 11 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 207 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974
  32 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 207 261
  (Polychromatic418967fa.accept_12_7_3_9_1_999 31 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 207 261 3 10 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 207 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 29 207 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 207 261 (Polychromatic418967fa.accept_13_2_12_1_1_343
  28 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 207 261 9 3 23 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 207 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 207 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 25 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 207 261 3 8 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 207 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 207 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 207 261 3 7 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 207 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 207 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 207 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 207 261 9 2 23 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 207 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 17 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 207 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 207 261 3 5 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 207 261 3 4 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 207 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 11 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 207 261 9 1 23 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 207 261
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 207 261 3 2 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 207 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 207 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 261
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 207 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 207 261 3 1 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 207 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 207 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 206 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 206 261 (accept_3_4 55 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 206 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 206 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 206 261 (accept_3_4 52 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 206 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 206 261 (accept_3_4 49 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 206 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 206 261 (accept_3_4 46 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 206 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 206 261
  (Polychromatic418967fa.accept_21_2_17_9_1_6895 44 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 206 261 (accept_3_4 43 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 206 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 206 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 206 261 (accept_3_4 40 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 206 261
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 38 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 206 261 (accept_3_4 37 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 206 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 206 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 206 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 206 261 (accept_3_4 34 206 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 206 261 (Polychromatic418967fa.accept_7_5_3_2_1_249
  33 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 206 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 206 261 (accept_3_4 31 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 206 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 206 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 206 261 (accept_3_4 28 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 206 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 206 261 (accept_3_4 25 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 206 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 206 261 (accept_3_4 22 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 206 261 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 206 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 206 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 206 261 (accept_3_4 19 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 206 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 206 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 206 261 (accept_3_4 16 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 206 261
  (Polychromatic418967fa.accept_20_14_6_1_1_3023 14 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 206 261 (accept_3_4 13 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 206 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 261 (accept_3_4 10 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 261 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 206 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 206 261 (accept_3_4 7 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  206 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 206 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 261 (accept_3_4 4 206 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 206 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 261 (accept_3_4 1 206 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 205 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 205 261 (accept_3_5 56 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 205 261 (Polychromatic418967fa.accept_19_17_15_14_1_3623 55 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 205 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 205 261 (accept_3_5 53 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 205 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 205 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 205 261 (accept_3_5 50 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 205 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 205 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 205 261 (accept_3_5 47 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 205 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 205 261
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 45 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 205 261 (accept_3_5 44 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 205 261 (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 205 261 (Polychromatic418967fa.accept_15_12_10_6_1_2134 42 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 205 261 (accept_3_5 41 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 205 261
  (Polychromatic418967fa.accept_6_4_1_3_1_77 40 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 205 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 205 261 (accept_3_5 38 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 205 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 205 261
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 205 261 (accept_3_5 35 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 205 261 (Polychromatic418967fa.accept_15_3_10_6_1_632 33 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 205 261 (accept_3_5 32 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 205 261 (Polychromatic418967fa.accept_15_1_10_6_1_631 31 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 205 261
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 205 261 (accept_3_5 29 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 205 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 27 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 205 261 (accept_3_5 26 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 205 261 (Polychromatic418967fa.accept_16_9_13_5_1_2238 25 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 205 261
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 205 261 (accept_3_5 23 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 205 261 (Polychromatic418967fa.accept_18_3_7_9_1_5486 21 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 205 261 (accept_3_5 20 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 205 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 205 261
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 261 (accept_3_5 17 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 261 (accept_3_5 14 205 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 261 (Polychromatic418967fa.accept_19_13_15_14_1_3549 13
  205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 261
  (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 205 261 (accept_3_5 11 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 205 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 205 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 261 (accept_3_5 8 205 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 261
  (Polychromatic418967fa.accept_19_7_15_14_1_3659 7 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 205 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 261 (accept_3_5 5 205 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 205 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 205 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 261 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 261 (accept_3_5 2 205
  261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 261
  (Polychromatic418967fa.accept_15_1_10_6_1_631 1 205 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 205 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 204 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 204 261 3 19 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 204 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 56 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 204 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 204 261 3 18 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 204 261 (Polychromatic418967fa.accept_21_11_15_9_1_3868 53 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 204 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 52 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 204 261 3 17 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 204 261 (Polychromatic418967fa.accept_13_11_9_1_1_1407 50 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 204 261
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 204 261 3 16 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 204 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 204 261
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 46 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 204 261 3 15 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 204 261 (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 204 261
  (Polychromatic418967fa.accept_14_1_8_9_1_1312 43 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 204 261 3 14 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 204 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 204 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 204 261 (Polychromatic418967fa.accept_16_8_12_5_1_200
  40 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 204 261 3 13 68 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 204 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 204 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319 37 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 204 261 3 12 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 204 261 (Polychromatic418967fa.accept_10_5_4_1_1_842
  35 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 204 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 204 261 3 11 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 204 261 (Polychromatic418967fa.accept_13_6_9_1_1_5604 32 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 204 261
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 204 261 3 10 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 204 261 (Polychromatic418967fa.accept_14_1_8_9_1_1312 29 204 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 204 261
  (Polychromatic418967fa.accept_13_2_9_1_1_67 28 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 204 261 3 9 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 204 261 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 204 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 204 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 204 261 3 8 68 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 204 261
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 204 261 (Polychromatic418967fa.accept_27_22_15_18_1_15990 22 204 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 204 261 3 7 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 204 261
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 204 261 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 204 261 3 6 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 204 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 204 261
  (Polychromatic418967fa.accept_15_1_9_6_1_1323 16 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 204 261 3 5 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 204 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 204 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 261 3 4 68 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 261
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 204 261 3 3 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 204 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 204 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 261
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 261 3 2 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 261 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 261 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 204 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 204 261 3 1 68 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 261
  (Polychromatic418967fa.accept_13_2_9_1_1_67 2 204 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 204 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 204 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 203 261 (Eq.refl Bool.true) (allA_succ_of_gcd 58 203 261 29 2 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 203 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 57 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 203 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 203 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 203 261 (accept_3_4 55 203 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 203 261
  (Polychromatic418967fa.accept_19_15_13_14_1_5015 53 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 203 261 (accept_3_4 52 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 203 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 51 203 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 203 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 203 261 (accept_3_4 49 203 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 203 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316
  48 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 203 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 203 261 (accept_3_4 46 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 203 261 (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 203 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 203 261 (accept_3_4 43 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 203 261
  (Polychromatic418967fa.accept_16_9_11_5_1_2279 41 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 203 261 (accept_3_4 40 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 203 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 203 261 (accept_3_4 37 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 203 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 203 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 203 261 (accept_3_4 34 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 203 261 (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 203 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 203 261 (accept_3_4 31 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 29 203 261 29 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 28 203 261 (accept_3_4 28 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 203 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 203
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 203 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 203 261 (accept_3_4 25 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 203 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 203 261 (Polychromatic418967fa.accept_16_7_11_5_1_4402 23 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 203 261 (accept_3_4 22 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 203 261 (Polychromatic418967fa.accept_23_21_19_8_1_15989 21
  203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 203 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 203 261 (accept_3_4 19 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 203 261 (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 261 (accept_3_4 16 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 203 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 203
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 261 (accept_3_4 13 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 261 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 261 (accept_3_4 10 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 261 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 203 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 261 (accept_3_4 7 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 261 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 261 (accept_3_4 4 203 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 203 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 261 (accept_3_4 1 203 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 202 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 202 261 (accept_3_5 59 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 202 261 (Polychromatic418967fa.accept_13_6_7_1_1_335 58 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 202 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 202 261 (accept_3_5 56 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 202 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 54 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 202 261 (accept_3_5 53 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 202 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 202 261 (accept_3_5 50 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 202 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 202 261
  (Polychromatic418967fa.accept_17_14_15_6_1_4819 48 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 202 261 (accept_3_5 47 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 202 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 202 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 202 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 202 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 202 261 (accept_3_5 44 202 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 202 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 42 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 202 261 (accept_3_5 41 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 202 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 202 261 (accept_3_5 38 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 202 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 202 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 202 261 (accept_3_5 35 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 202 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 202 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 33 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 202 261 (accept_3_5 32 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 202 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 202 261
  (Polychromatic418967fa.accept_12_6_10_9_1_531 30 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 202 261 (accept_3_5 29 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 202 261 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 202 261 (accept_3_5 26 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 202 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 202 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 202 261 (accept_3_5 23 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 202 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 202 261 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 261 (accept_3_5 20 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 202 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 261 (accept_3_5 17 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 261 (accept_3_5 14 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 261 (accept_3_5 11 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 261 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 261 (accept_3_5 8 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 261
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 261 (accept_3_5 5 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 202 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 261 (accept_3_5 2 202 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 202 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 201 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 201 261 3 20 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 201 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 201 261
  (Polychromatic418967fa.accept_17_7_14_6_1_4882 58 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 201 261 3 19 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 201 261 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 201 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 201 261
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 55 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 201 261 3 18 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 201 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 201 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 52
  201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 201 261 3 17 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 201 261
  (Polychromatic418967fa.accept_11_6_3_8_1_843 50 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 201 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 201 261 3 16 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 201 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808
  47 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 201 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 201 261 3 15 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 201 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 201 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 201 261
  (Polychromatic418967fa.accept_16_11_9_5_1_4412 43 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 201 261 3 14 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 201 261 (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 201 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 201 261
  (Polychromatic418967fa.accept_21_19_12_9_1_9957 40 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 201 261 3 13 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 201 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 201 261
  (Polychromatic418967fa.accept_17_3_14_6_1_3742 37 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 201 261 3 12 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 201 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 201 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 201 261
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 201 261 3 11 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 201 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 201 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 31
  201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 201 261 3 10 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 201 261
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 201 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 201 261 3 9 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 201 261 (Polychromatic418967fa.accept_18_8_3_9_1_4232
  26 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 201 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 201 261 3 8 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 201 261 (Polychromatic418967fa.accept_21_2_12_9_1_5324 23 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 201 261 (Polychromatic418967fa.accept_13_9_6_1_1_2902 22 201
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 201 261 3 7 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 201 261
  (Polychromatic418967fa.accept_8_4_1_5_1_186 20 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 261 (Polychromatic418967fa.accept_18_1_3_9_1_328 19 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 201 261 3 6 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 261
  (Polychromatic418967fa.accept_11_5_3_8_1_454 16 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 201 261 3 5 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 201 261 (Polychromatic418967fa.accept_16_14_9_5_1_4388 14 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 261 (Polychromatic418967fa.accept_16_13_9_5_1_3302 13 201
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 201 261 3 4 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 201 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 201 261 3 3 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 261 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 201 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 261
  (Polychromatic418967fa.accept_13_7_6_1_1_368 7 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 201 261 3 2 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 261 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 201 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 261 3 1 67 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 261
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 201 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 261 (Polychromatic418967fa.accept_16_1_9_5_1_5443 1 201 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 200 261 (Eq.refl Bool.true) (allA_succ_of_accept 61 200 261 (accept_3_4 61 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 200 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 200 261 (accept_3_4 58 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 200 261 (Polychromatic418967fa.accept_15_12_5_6_1_2148 57 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 200 261 (Polychromatic418967fa.accept_13_4_5_1_1_833 56 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 200 261 (accept_3_4 55 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 200 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 200 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 200 261 (accept_3_4 52 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 200 261 (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 200 261 (Polychromatic418967fa.accept_19_12_10_14_1_6353 50 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 200 261 (accept_3_4 49 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 200 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 200 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 200 261 (accept_3_4 46 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 200 261 (Polychromatic418967fa.accept_13_6_5_1_1_834 45 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 200 261 (Polychromatic418967fa.accept_14_2_4_9_1_2121 44 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 200 261 (accept_3_4 43 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 200 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 42 200
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 200 261 (accept_3_4 40 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 200 261 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 200 261 (Polychromatic418967fa.accept_11_5_2_8_1_866 38 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 200 261 (accept_3_4 37 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 200 261 (Polychromatic418967fa.accept_16_4_8_5_1_3317 36 200
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 200 261 (accept_3_4 34 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 200 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 200 261 (Polychromatic418967fa.accept_13_6_5_1_1_834 32 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 200 261 (accept_3_4 31 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 200 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 30 200
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 200 261 (accept_3_4 28 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 200 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 200 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 200 261 (accept_3_4 25 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 200 261 (Polychromatic418967fa.accept_17_7_13_6_1_811 24 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 200 261 (accept_3_4 22 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 200 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 200 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 200 261 (accept_3_4 19 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 200 261 (Polychromatic418967fa.accept_12_6_8_9_1_553 18 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 200 261 (accept_3_4 16 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 200 261 (Polychromatic418967fa.accept_19_15_10_14_1_3652 15 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 200 261 (Polychromatic418967fa.accept_15_14_5_6_1_6168 14 200 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 200 261 (accept_3_4 13 200 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 200 261 (Polychromatic418967fa.accept_7_5_4_2_1_235
  12 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 200 261 (accept_3_4 10 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  200 261 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 200 261 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 261 (accept_3_4 7 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 200 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 200 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 200 261
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 200 261 (accept_3_4 4 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  200 261 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 200 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 200 261 (Polychromatic418967fa.accept_14_2_4_9_1_2121 2 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 200 261 (accept_3_4 1 200 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 200 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  199 261 (Eq.refl Bool.true) (allA_succ_of_accept 62 199 261 (accept_3_5 62 199 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 199 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 199 261
  (Polychromatic418967fa.accept_16_12_7_5_1_1412 60 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 199 261 (accept_3_5 59 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 199 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 199 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 199 261 (accept_3_5 56 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 199 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 199 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 199 261 (accept_3_5 53 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 199 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 199 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 51 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 199 261 (accept_3_5 50 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 199 261 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 199
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 199 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 199 261 (accept_3_5 47 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 199 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 199 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 199 261 (accept_3_5 44 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 199 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 199 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 199 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 199 261 (accept_3_5 41 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 199 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 199 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 39 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 199 261 (accept_3_5 38 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 199 261 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 199
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 199 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 199 261 (accept_3_5 35 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 199 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 199 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 199 261 (accept_3_5 32 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 199 261 (Polychromatic418967fa.accept_13_5_4_1_1_364 31 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 199 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 199 261 (accept_3_5 29 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 199 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 199 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 199 261 (accept_3_5 26 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 199 261 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 199 261
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 199 261 (accept_3_5 23 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 199 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 199 261 (Polychromatic418967fa.accept_18_3_1_9_1_1929 21 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 261 (accept_3_5 20 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 199 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 261 (accept_3_5 17 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 261 (accept_3_5 14 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 261 (accept_3_5 11 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 261 (Polychromatic418967fa.accept_15_9_4_6_1_3075 9 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 261 (accept_3_5 8 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 261 (Polychromatic418967fa.accept_21_7_10_9_1_6848 7 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 261 (accept_3_5 5 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 199 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 261 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 261 (accept_3_5 2 199 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 199 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 198 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 198 261 9 7 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 198 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 62 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 198 261 (Polychromatic418967fa.accept_15_1_3_6_1_621 61 198
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 198 261 3 20 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 198 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 198 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 58 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 198 261 3 19 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 198 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  56 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 198 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 55 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 198 261 9 6 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 198 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 198 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 52 198
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 198 261 3 17 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 198 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 50 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 198 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 198 261 3 16 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47
  198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 198 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 46 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 198 261 9 5 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 198 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 44 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 198 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 198 261 3 14 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 198 261
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 198 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 40 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 198 261 3 13 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 198 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 38
  198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 198 261
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 198 261 9 4 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 198 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 34 198
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 198 261 3 11 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 198 261
  (Polychromatic418967fa.accept_12_8_6_9_1_1608 32 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 198 261 3 10 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 198 261 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  29 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 198 261
  (Polychromatic418967fa.accept_12_4_6_9_1_548 28 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 198 261 9 3 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 198 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 26 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 198 261 (Polychromatic418967fa.accept_14_11_2_9_1_5873 25 198
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 198 261 3 8 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 198 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 198 261 (Polychromatic418967fa.accept_12_10_6_9_1_549 22 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 198 261 3 7 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 198 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608
  20 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 261
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 198 261 9 2 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 198 261 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 16 198
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 198 261 3 5 66 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 198 261
  (Polychromatic418967fa.accept_12_2_6_9_1_19 14 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 261 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 261 3 4 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 261
  (Polychromatic418967fa.accept_12_10_6_9_1_549 10 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 198 261 9 1 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 198 261 (Polychromatic418967fa.accept_12_8_6_9_1_1608 8 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 261 3 2 66 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 261
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 261 (Polychromatic418967fa.accept_12_4_6_9_1_548 4 198 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 261 3 1 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 261 (Polychromatic418967fa.accept_12_2_6_9_1_19 2 198 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 261
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 198 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 197 261 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 197 261 (accept_3_4 64 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 197 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 63 197 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 197 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 197 261 (accept_3_4 61 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 197 261
  (Polychromatic418967fa.accept_19_3_7_14_1_3669 60 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 197 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 197 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 197 261 (accept_3_4 58 197 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 197 261 (Polychromatic418967fa.accept_15_12_2_6_1_2127 57 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 197 261 (accept_3_4 55 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 197 261 (Polychromatic418967fa.accept_10_4_7_1_1_471 54 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 197 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 53 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 197 261 (accept_3_4 52 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 197 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 51 197
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 197 261 (accept_3_4 49 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 197 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 197 261 (Polychromatic418967fa.accept_24_23_5_21_1_5462 47 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 197 261 (accept_3_4 46 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 197 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 197 261 (accept_3_4 43 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 197 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 197 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 197 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 197 261 (accept_3_4 40 197 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 197 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 39 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 197 261 (accept_3_4 37 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 197 261 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 197 261 (Polychromatic418967fa.accept_13_9_2_1_1_813 35 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 197 261 (accept_3_4 34 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 197 261 (Polychromatic418967fa.accept_17_16_10_6_1_7313 33 197
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 197 261 (accept_3_4 31 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 197 261 (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 197 261 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 197 261 (accept_3_4 28 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 197 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 197 261 (accept_3_4 25 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 197 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 197 261 (Polychromatic418967fa.accept_15_8_2_6_1_2125 23 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 261 (accept_3_4 22 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 197 261 (Polychromatic418967fa.accept_17_4_10_6_1_4869 21 197
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 197 261 (accept_3_4 19 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 197 261 (Polychromatic418967fa.accept_19_18_7_14_1_5012 18 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 197 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 197 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 261 (accept_3_4 16 197 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 261 (Polychromatic418967fa.accept_12_3_5_9_1_176 15 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 197 261 (accept_3_4 13 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 197 261 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 197 261 (Polychromatic418967fa.accept_15_11_2_6_1_3010 11 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 261 (accept_3_4 10 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 261 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 197 261 (accept_3_4 7 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 261 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 261 (Polychromatic418967fa.accept_23_5_13_8_1_5978 5 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 261 (accept_3_4 4 197 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 261 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 197 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 261
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 261 (accept_3_4 1 197 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 196 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 196 261 (accept_3_5 65 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 196 261 (Polychromatic418967fa.accept_19_7_6_14_1_11872 64 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 196 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 63 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 196 261 (accept_3_5 62 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 196 261
  (Polychromatic418967fa.accept_16_12_4_5_1_2273 60 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 196 261 (accept_3_5 59 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 196 261 (Polychromatic418967fa.accept_19_1_6_14_1_15982 58 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 196 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 196 261 (accept_3_5 56 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 196 261
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 196 261 (accept_3_5 53 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 196 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 196 261 (Polychromatic418967fa.accept_18_15_16_9_1_4299 51 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 196 261 (accept_3_5 50 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 196 261
  (Polychromatic418967fa.accept_15_3_1_6_1_206 48 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 196 261 (accept_3_5 47 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 196 261 (Polychromatic418967fa.accept_19_8_6_14_1_5009 46 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 196 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 196 261 (accept_3_5 44 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 196 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 196 261 (accept_3_5 41 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 196 261 (Polychromatic418967fa.accept_15_10_1_6_1_3033 40 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 196 261 (Polychromatic418967fa.accept_15_9_1_6_1_657 39 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 196 261 (accept_3_5 38 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 196 261
  (Polychromatic418967fa.accept_21_15_7_9_1_11550 36 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 196 261 (accept_3_5 35 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 196 261 (Polychromatic418967fa.accept_21_13_7_9_1_2528 34 196 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 196 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 196 261 (accept_3_5 32 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 196 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 30 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 196 261 (accept_3_5 29 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 196 261 (Polychromatic418967fa.accept_16_12_4_5_1_2273 28 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 196 261 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 261 (accept_3_5 26 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 261
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 261 (accept_3_5 23 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 261 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 261 (accept_3_5 20 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 18 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 261 (accept_3_5 17 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 261 (Polychromatic418967fa.accept_17_16_9_6_1_3723 16 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 261 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 261 (accept_3_5 14 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 196 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 261
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 261 (accept_3_5 11 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 261 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 261 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 261 (accept_3_5 8 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 261
  (Polychromatic418967fa.accept_12_6_4_9_1_544 6 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 261 (accept_3_5 5 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 261 (Polychromatic418967fa.accept_23_4_12_8_1_15988 4 196 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 261 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 261 (accept_3_5 2 196 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 261 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 195 261 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 195 261 3 22 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 195 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 65 195 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 195 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 64
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 195 261 3 21 65 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 62 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 195 261 (Polychromatic418967fa.accept_12_1_3_9_1_174 61 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 195 261 3 20 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 195 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 58 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 195 261 3 19 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 195 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 195 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 195 261 (Polychromatic418967fa.accept_12_7_3_9_1_999
  55 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 195 261 3 18 65 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 195 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 195 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 195 261 3 17 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 195 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 195 261
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 195 261 3 16 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 195 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 47 195 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 46 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 195 261 3 15 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 195 261 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 195 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 195 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 195 261 3 14 65 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 195 261
  (Polychromatic418967fa.accept_12_5_3_9_1_541 41 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 195 261 (Polychromatic418967fa.accept_16_8_3_5_1_5512 40 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 195 261 3 13 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 195 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 195 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 37 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 195 261 3 12 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 195 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630 35 195 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 195 261 3 11 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 195 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 195 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 195 261 (Polychromatic418967fa.accept_7_3_6_2_1_90 31
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 195 261 3 10 65 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 195 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 195 261 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 195 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 195 261 3 9 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 195 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 195 261 3 8 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 195 261 (Polychromatic418967fa.accept_12_11_3_9_1_1630
  23 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 261
  (Polychromatic418967fa.accept_4_2_3_1_1_2 22 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 195 261 3 7 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 195 261 (Polychromatic418967fa.accept_21_20_6_9_1_6872 20 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 195 261 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 195
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 195 261 3 6 65 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 195 261
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 261 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 261 3 5 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14
  195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 261
  (Polychromatic418967fa.accept_12_1_3_9_1_174 13 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 195 261 3 4 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 195 261 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 195 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 261 3 3 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 261
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 261 (Polychromatic418967fa.accept_12_7_3_9_1_999 7 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 261 3 2 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 261 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 195 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 261
  (Polychromatic418967fa.accept_7_4_6_2_1_451 4 195 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 261 3 1 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 261 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 195 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 194 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 194 261 (accept_3_4 67 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 194 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 194 261 (accept_3_4 64 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 194 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 194 261
  (Polychromatic418967fa.accept_23_16_10_8_1_15987 62 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 194 261 (accept_3_4 61 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 194 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 194 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 194 261 (accept_3_4 58 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 194 261 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  57 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 194 261
  (Polychromatic418967fa.accept_19_18_4_14_1_14577 56 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 194 261 (accept_3_4 55 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 194 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 54 194 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 194 261 (accept_3_4 52 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 51
  194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 194 261
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 50 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 194 261 (accept_3_4 49 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 194 261 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 194 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 194 261 (accept_3_4 46 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 194 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 45
  194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 194 261
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 194 261 (accept_3_4 43 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 194 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 42 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 194 261 (accept_3_4 40 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 194 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 194 261
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 194 261 (accept_3_4 37 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 194 261 (Polychromatic418967fa.accept_21_15_5_9_1_5315 36 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 194 261 (accept_3_4 34 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 194 261 (Polychromatic418967fa.accept_17_16_7_6_1_7343 33 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 194 261
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 194 261 (accept_3_4 31 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 194 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 30 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 194 261 (accept_3_4 28 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 194 261
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 194 261 (accept_3_4 25 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 194 261 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 194 261 (accept_3_4 22 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 194 261 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 194 261
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 194 261 (accept_3_4 19 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 194 261 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 194 261 (accept_3_4 16 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 194 261
  (Polychromatic418967fa.accept_17_14_7_6_1_11222 14 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 194 261 (accept_3_4 13 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 194 261 (Polychromatic418967fa.accept_21_12_5_9_1_8504 12 194 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 261 (accept_3_4 10 194 261
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 261 (Polychromatic418967fa.accept_15_9_14_6_1_3004
  9 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 261
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 261 (accept_3_4 7 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 261 (Polychromatic418967fa.accept_12_6_2_9_1_537 6 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 261 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 261 (accept_3_4 4 194 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 261 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 261
  (Polychromatic418967fa.accept_13_2_12_1_1_343 2 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 261 (accept_3_4 1 194 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 193 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 193 261 (accept_3_5 68 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 193 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 67 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 193 261 (Polychromatic418967fa.accept_19_9_3_14_1_2400 66 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 193 261 (accept_3_5 65 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 193 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 193 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 63 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 193 261 (accept_3_5 62 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 193 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 193 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 193 261 (accept_3_5 59 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 193 261
  (Polychromatic418967fa.accept_16_9_1_5_1_2282 57 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 193 261 (accept_3_5 56 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 193 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 193 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 193 261 (accept_3_5 53 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 193 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 51 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 193 261 (accept_3_5 50 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 193 261 (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 193 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 193 261 (accept_3_5 47 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 193 261
  (Polychromatic418967fa.accept_16_13_1_5_1_5469 45 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 193 261 (accept_3_5 44 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 193 261 (Polychromatic418967fa.accept_19_5_3_14_1_3573 43 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 193 261 (Polychromatic418967fa.accept_10_2_3_1_1_481 42 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 193 261 (accept_3_5 41 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 193 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 193 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 39 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 193 261 (accept_3_5 38 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 193 261 (Polychromatic418967fa.accept_15_7_13_6_1_696 37 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 193 261 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 193 261 (accept_3_5 35 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 193 261
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 193 261 (accept_3_5 32 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 193 261 (Polychromatic418967fa.accept_16_15_1_5_1_2265 31 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 193 261 (Polychromatic418967fa.accept_14_2_11_9_1_2925 30 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 193 261 (accept_3_5 29 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 193 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 261
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 193 261 (accept_3_5 26 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 193 261 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 261 (Polychromatic418967fa.accept_18_6_13_9_1_4218 24 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 261 (accept_3_5 23 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 193 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 261
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 261 (accept_3_5 20 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 261 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 261 (accept_3_5 17 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 193 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 261
  (Polychromatic418967fa.accept_12_3_1_9_1_202 15 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 261 (accept_3_5 14 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 261 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 261 (accept_3_5 11 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 261
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 261 (accept_3_5 8 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 261 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 261 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 261 (accept_3_5 5 193 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 261 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 261
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 261 (accept_3_5 2 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 261 (Polychromatic418967fa.accept_23_1_9_8_1_15986 1 193 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 261))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 192
  261 (Eq.refl Bool.true) (allA_succ_of_gcd 69 192 261 3 23 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 192 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 192 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 192 261
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 192 261 3 22 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 192 261 (Polychromatic418967fa.accept_15_5_12_6_1_639 65 192 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 192 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 192 261 3 21 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 192 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 62 192 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 192 261 (Polychromatic418967fa.accept_7_5_3_2_1_249
  61 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 192 261 3 20 64 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 192 261
  (Polychromatic418967fa.accept_10_9_2_1_1_840 59 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 192 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 192 261 3 19 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 192 261 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 192 261
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 192 261 3 18 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 192 261 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 192 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 192 261
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 192 261 3 17 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 192 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 192 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 192 261 (Polychromatic418967fa.accept_10_9_2_1_1_840
  49 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 192 261 3 16 64 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 192 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 47 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 192 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 192 261 3 15 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 192 261 (Polychromatic418967fa.accept_21_2_3_9_1_1317
  44 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 192 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 192 261 3 14 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 192 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 192 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 192 261 (Polychromatic418967fa.accept_7_5_3_2_1_249
  40 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 192 261 3 13 64 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 192 261
  (Polychromatic418967fa.accept_17_4_5_6_1_8717 38 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 192 261 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 192 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 192 261 3 12 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 192 261
  (Polychromatic418967fa.accept_11_2_5_8_1_470 35 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 192 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 192 261 3 11 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 192 261 (Polychromatic418967fa.accept_15_2_12_6_1_3063
  32 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 192 261
  (Polychromatic418967fa.accept_19_12_2_14_1_10618 31 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 192 261 3 10 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 192 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 192 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 261
  (Polychromatic418967fa.accept_17_11_5_6_1_4928 28 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 192 261 3 9 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 192 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 261 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 192
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 261 3 8 64 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 261
  (Polychromatic418967fa.accept_10_3_2_1_1_839 23 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 192 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 192 261 3 7 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 192 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 261
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 261 3 6 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 192 261 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 261 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 192
  261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 192 261 3 5 64 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 192 261
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 192 261 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 261 3 4 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 261
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 192 261 (Polychromatic418967fa.accept_15_10_12_6_1_3000 10 192 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 192 261 3 3 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 192 261
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 261 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 261 3 2 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 261 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 261
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 192 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 192 261 3 1 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 192 261 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 192 261 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 261 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 192 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 191 261 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 191 261 (accept_3_4 70 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 191 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 69 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 191 261 (accept_3_4 67 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 191 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 65 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 191 261 (accept_3_4 64 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 191 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 63 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 191 261 (accept_3_4 61 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 191 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 60 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 191 261
  (Polychromatic418967fa.accept_19_2_1_14_1_3663 59 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 191 261 (accept_3_4 58 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 191 261 (Polychromatic418967fa.accept_13_5_9_1_1_1405 57 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 191 261 (accept_3_4 55 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 191 261
  (Polychromatic418967fa.accept_17_2_4_6_1_1619 53 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 191 261 (accept_3_4 52 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 191 261 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 191 261 (accept_3_4 49 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 191 261 (Polychromatic418967fa.accept_15_3_11_6_1_3083 48 191 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 191 261
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 191 261 (accept_3_4 46 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 191 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 191 261 (accept_3_4 43 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 191 261
  (Polychromatic418967fa.accept_13_2_9_1_1_67 41 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 191 261 (accept_3_4 40 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 191 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 39 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 191 261 (accept_3_4 37 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 191 261 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 191 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 191 261
  (Polychromatic418967fa.accept_15_5_11_6_1_692 35 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 191 261 (accept_3_4 34 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 191 261 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 191 261 (accept_3_4 31 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 261
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 191 261 (accept_3_4 28 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 191 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 27 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 261 (accept_3_4 25 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 191 261 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 191 261
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 261
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 261 (accept_3_4 22 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 261 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 261 (accept_3_4 19 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 261
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 261 (accept_3_4 16 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 15 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 261 (accept_3_4 13 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 261 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 261
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 191 261 (accept_3_4 10 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  191 261 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 191 261 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 261 (accept_3_4 7 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 261 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 261
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 261 (accept_3_4 4 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 261 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 191 261 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 261 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 261 (accept_3_4 1 191 261 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 261)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_261_segment_002))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


