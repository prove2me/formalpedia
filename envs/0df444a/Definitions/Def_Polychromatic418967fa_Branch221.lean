-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch221
-- name    : Polychromatic418967fa_Branch221
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:24:53.476255+00:00
-- url     : https://prove2.me/theorems/343e185e-4a59-4bf9-b379-3b486fcbcd19
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch221_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_221 : allB 221 221 :=
  allB_succ' 2 220 221 (Eq.refl Bool.true) (allA_of_3_0 2 220 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  219 221 (Eq.refl Bool.true) (allA_succ_of_accept 2 219 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 219 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 221 (accept_3_2 1 219 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 221))) (allB_succ' 4 218 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 218 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 218 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 218 221 (Polychromatic418967fa.accept_19_2_9_12_1_2237 2 218
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 218 221 (accept_3_2 1 218 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 218 221)))) (allB_succ' 5 217 221 (Eq.refl Bool.true) (allA_of_3_0
  5 217 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 216 221 (Eq.refl Bool.true) (allA_succ_of_accept 5
  216 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 216 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 216 221 (accept_3_2 4 216 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 216 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 216 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 216 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 221 (accept_3_2 1 216 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 221)))))) (allB_succ' 7 215 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 6 215 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 215 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 215 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 215 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 215 221 (accept_3_2 4 215 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 215 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3
  215 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 215 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 215 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 215 221 (accept_3_2 1 215 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 215 221)))))))
  (allB_succ' 8 214 221 (Eq.refl Bool.true) (allA_of_3_0 8 214 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  9 213 221 (Eq.refl Bool.true) (allA_succ_of_accept 8 213 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 213 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 213 221 (accept_3_2 7 213 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  213 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 221
  (Polychromatic418967fa.accept_19_5_4_12_1_7773 5 213 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 221 (accept_3_2 4 213 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 213 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 213 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 221 (accept_3_2 1 213 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 221))))))))) (allB_succ' 10 212 221 (Eq.refl Bool.true) (allA_succ_of_accept 9 212
  221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 212 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 212 221 (Polychromatic418967fa.accept_16_8_4_13_1_1014 8 212 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 212 221 (accept_3_2 7 212 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 212 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 212 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 212 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  212 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 212 221 (accept_3_2 4 212
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 212 221 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 212 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 221
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 212 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 212 221 (accept_3_2 1 212 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212
  221)))))))))) (allB_succ' 11 211 221 (Eq.refl Bool.true) (allA_of_3_0 11 211 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 210 221 (Eq.refl Bool.true) (allA_succ_of_accept 11 210 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 210 221 (accept_3_2 10 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  210 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 9 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 210 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 210 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 221 (accept_3_2 7 210 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 210 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 210 221
  (Polychromatic418967fa.accept_16_5_2_13_1_1007 5 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 210 221 (accept_3_2 4 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  210 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 210 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 210 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 221 (accept_3_2 1 210 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 210 221)))))))))))) (allB_succ' 13 209 221 (Eq.refl Bool.true) (allA_succ_of_accept 12
  209 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 209 221 (Polychromatic418967fa.accept_23_11_2_14_1_11528 11 209 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 209 221 (accept_3_2 10 209 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 209 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 209 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 209 221 (accept_3_2 7 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  209 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 209 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 209 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 221 (accept_3_2 4 209 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 209 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 209 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 209 221 (accept_3_2 1 209 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209
  221))))))))))))) (allB_succ' 14 208 221 (Eq.refl Bool.true) (allA_of_3_0 14 208 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 207 221 (Eq.refl Bool.true) (allA_succ_of_accept 14 207 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 207 221 (accept_3_2 13 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 207 221 (Polychromatic418967fa.accept_16_12_15_13_1_3872 12 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 221 (Polychromatic418967fa.accept_20_11_7_1_1_8874 11 207 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 221 (accept_3_2 10 207 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9
  207 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 207 221 (accept_3_2 7 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  207 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 207 221 (Polychromatic418967fa.accept_19_5_17_12_1_6120 5 207 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 221 (accept_3_2 4 207 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 221 (Polychromatic418967fa.accept_16_3_15_13_1_2825 3 207
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 221 (accept_3_2 1 207 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207
  221))))))))))))))) (allB_succ' 16 206 221 (Eq.refl Bool.true) (allA_succ_of_accept 15 206 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 206 221 (Polychromatic418967fa.accept_18_14_8_5_1_860 14 206 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 206 221 (accept_3_2 13 206 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 206 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 206 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 206 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11
  206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 206 221 (accept_3_2 10
  206 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 206 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 206 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 206 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 221 (accept_3_2 7 206 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 206 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 206 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 5
  206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 221 (accept_3_2 4 206
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 221 (Polychromatic418967fa.accept_4_3_2_1_1_50
  3 206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 206 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 221 (accept_3_2 1 206 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  221)))))))))))))))) (allB_succ' 17 205 221 (Eq.refl Bool.true) (allA_of_3_0 17 205 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 204 221 (Eq.refl Bool.true) (allA_succ_of_gcd 17 204 221 17 1 12 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 204 221 (accept_3_2 16 204 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 204 221 (Polychromatic418967fa.accept_10_5_4_1_1_842
  15 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 221
  (Polychromatic418967fa.accept_25_14_4_21_1_13212 14 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 204 221 (accept_3_2 13 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 204 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 204 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 204 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 221 (accept_3_2 10 204 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 204 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9
  204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 204 221 (accept_3_2 7 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  204 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 204 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 204 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 204 221 (accept_3_2 4 204 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 204 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 221 (accept_3_2 1 204 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204
  221)))))))))))))))))) (allB_succ' 19 203 221 (Eq.refl Bool.true) (allA_succ_of_accept 18 203 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 203 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 203 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 203 221 (accept_3_2 16 203 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 203 221 (Polychromatic418967fa.accept_22_15_5_1_1_8441 15 203 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 203 221 (accept_3_2 13 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 203 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 12 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 221 (Polychromatic418967fa.accept_19_11_13_12_1_6259 11 203 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 221 (accept_3_2 10 203 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 221 (Polychromatic418967fa.accept_22_9_5_1_1_2204 9 203 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 221
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 221 (accept_3_2 7 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 203 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 221 (accept_3_2 4 203 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 203 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 221 (accept_3_2 1 203 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  221))))))))))))))))))) (allB_succ' 20 202 221 (Eq.refl Bool.true) (allA_of_3_0 20 202 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 201 221 (Eq.refl Bool.true) (allA_succ_of_accept 20 201 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 201 221 (accept_3_2 19 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 201 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 201 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 221 (accept_3_2 16 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 201 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 221 (accept_3_2 13 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 221 (accept_3_2 10 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 201 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 221 (accept_3_2 7 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 221 (Polychromatic418967fa.accept_15_5_6_11_1_854 5 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 221 (accept_3_2 4 201 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 201 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 221 (accept_3_2 1 201 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  221))))))))))))))))))))) (allB_succ' 22 200 221 (Eq.refl Bool.true) (allA_succ_of_accept 21 200 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 200 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 20 200 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 200 221 (accept_3_2 19 200 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 200 221 (Polychromatic418967fa.accept_22_18_2_1_1_6765 18 200 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 200 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 200 221 (accept_3_2 16 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 200 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 200 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 200 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 200 221 (accept_3_2 13 200 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 200 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 200 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 200 221
  (Polychromatic418967fa.accept_16_11_8_13_1_3844 11 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 200 221 (accept_3_2 10 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 200 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 200 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 200 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 221 (accept_3_2 7 200 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 200 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 200 221
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 5 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 200 221 (accept_3_2 4 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  200 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 200 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 200 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 200 221 (accept_3_2 1 200 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 200 221)))))))))))))))))))))) (allB_succ' 23 199 221 (Eq.refl Bool.true) (allA_of_3_0
  23 199 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 198 221 (Eq.refl Bool.true) (allA_succ_of_accept 23
  198 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 198 221 (accept_3_2 22 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 198 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 198 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 198 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 221 (accept_3_2 19 198 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 221
  (Polychromatic418967fa.accept_21_18_9_11_1_7082 18 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 198 221 (Polychromatic418967fa.accept_20_17_18_1_1_8880 17 198 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 198 221 (accept_3_2 16 198 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 198 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 198 221 (accept_3_2 13 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 198 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 198 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 198 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 198 221 (accept_3_2 10 198 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 198 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 198 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 221
  (Polychromatic418967fa.accept_15_8_3_11_1_849 8 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 198 221 (accept_3_2 7 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  198 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 198 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 198 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 198 221 (accept_3_2 4 198 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 221
  (Polychromatic418967fa.accept_21_2_9_11_1_13096 2 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 221 (accept_3_2 1 198 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  221)))))))))))))))))))))))) (allB_succ' 25 197 221 (Eq.refl Bool.true) (allA_succ_of_accept 24 197 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 197 221 (Polychromatic418967fa.accept_19_4_7_12_1_6201 23 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 197 221 (accept_3_2 22 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 197 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 197 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 221 (Polychromatic418967fa.accept_9_2_8_5_1_228
  20 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 221 (accept_3_2 19
  197 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 221
  (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 197 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 221 (accept_3_2 16 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 197 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 197 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 221 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 221 (accept_3_2 13
  197 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 197 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 221 (accept_3_2 10 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 197 221 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 197 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 221 (Polychromatic418967fa.accept_16_8_5_13_1_1021
  8 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 221 (accept_3_2 7
  197 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 6 197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 197 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 221 (accept_3_2 4 197 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 197 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 197 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  197 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 221 (accept_3_2 1 197
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197 221))))))))))))))))))))))))) (allB_succ' 26 196 221
  (Eq.refl Bool.true) (allA_of_3_0 26 196 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 195 221 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 195 221 13 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 195 221 (accept_3_2 25 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 195 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 195 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 195 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 221 (accept_3_2 22 195 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21
  195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 221 (accept_3_2 19 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 195 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 221 (accept_3_2 16 195 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 195 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 195 221 13 1 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 195 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 221 (Polychromatic418967fa.accept_9_2_6_5_1_227
  11 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 221 (accept_3_2 10
  195 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 221 (accept_3_2 7 195 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5
  195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 221 (accept_3_2 4 195
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 221 (Polychromatic418967fa.accept_7_3_6_4_1_30
  3 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 221 (accept_3_2 1 195 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  221))))))))))))))))))))))))))) (allB_succ' 28 194 221 (Eq.refl Bool.true) (allA_succ_of_accept 27 194 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 194 221 (Polychromatic418967fa.accept_18_8_14_5_1_2778 26 194 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 194 221 (accept_3_2 25 194 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 194 221 (Polychromatic418967fa.accept_19_5_4_12_1_7773 24 194 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 194 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 194 221 (accept_3_2 22 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 194 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 194 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 221 (accept_3_2 19 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 194 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 194 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 194 221
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 194 221 (accept_3_2 16 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 194 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 194 221 (Polychromatic418967fa.accept_21_14_5_11_1_8676 14 194 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 221 (accept_3_2 13 194 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 12
  194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 221 (accept_3_2 10 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 221 (accept_3_2 7 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 194 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 221 (accept_3_2 4 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 221 (accept_3_2 1 194 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 221)))))))))))))))))))))))))))) (allB_succ' 29 193 221 (Eq.refl Bool.true)
  (allA_of_3_0 29 193 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 192 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 192 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 221 (accept_3_2 28 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 192 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 192 221 (Polychromatic418967fa.accept_9_8_3_5_1_241
  26 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 192 221 (accept_3_2 25
  192 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 192 221
  (Polychromatic418967fa.accept_9_6_3_5_1_240 24 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 192 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 221 (accept_3_2 22 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 192 221 (Polychromatic418967fa.accept_14_7_10_11_1_8112 21 192 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 192 221 (accept_3_2 19 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 192 221 (Polychromatic418967fa.accept_21_18_3_11_1_7049 18 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 192 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 221 (accept_3_2 16 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 192 221
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 192 221 (accept_3_2 13 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 192 221 (Polychromatic418967fa.accept_21_12_3_11_1_10078 12 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11
  192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 221 (accept_3_2 10
  192 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 221
  (Polychromatic418967fa.accept_10_9_2_1_1_840 9 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 221 (accept_3_2 7 192 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 221
  (Polychromatic418967fa.accept_22_5_16_1_1_13211 5 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 221 (accept_3_2 4 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 192 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 221 (accept_3_2 1 192 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192 221)))))))))))))))))))))))))))))) (allB_succ' 31 191 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 30 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 191 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 191 221 (Polychromatic418967fa.accept_26_3_9_13_1_13210 29 191
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 191 221 (accept_3_2 28 191
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 191 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 191 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 191 221 (accept_3_2 25 191 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 191 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 221
  (Polychromatic418967fa.accept_19_4_1_12_1_4803 23 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 191 221 (accept_3_2 22 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 191 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 191 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 221 (accept_3_2 19 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 191 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 191 221 (accept_3_2 16 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 191 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 221 (accept_3_2 13 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 221
  (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 221 (accept_3_2 10 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 221 (Polychromatic418967fa.accept_19_9_1_12_1_6234 9 191 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 191 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 221 (accept_3_2 7 191 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 221 (accept_3_2 4 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 191 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 221 (accept_3_2 1 191 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 221))))))))))))))))))))))))))))))) (allB_succ' 32 190 221 (Eq.refl Bool.true)
  (allA_of_3_0 32 190 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 189 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 189 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 189 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 221 (accept_3_2 31 189 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 189 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 30 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 221
  (Polychromatic418967fa.accept_23_6_5_14_1_13209 29 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 189 221 (accept_3_2 28 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 189 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 189 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 189 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 221 (accept_3_2 25 189 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 221
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 221 (Polychromatic418967fa.accept_24_23_21_5_1_9781 23 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 221 (accept_3_2 22 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 189
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 221 (accept_3_2 19 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 17 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 221 (accept_3_2 16 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 189
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 221 (accept_3_2 13 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 221 (Polychromatic418967fa.accept_19_11_18_12_1_4802 11 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 221 (accept_3_2 10 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 221 (Polychromatic418967fa.accept_19_9_18_12_1_2286 9 189
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 221 (accept_3_2 7 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 189 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 221 (accept_3_2 4 189 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 189 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 221 (accept_3_2 1 189 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  221))))))))))))))))))))))))))))))))) (allB_succ' 34 188 221 (Eq.refl Bool.true) (allA_succ_of_accept 33 188 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 33 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 188 221 (Polychromatic418967fa.accept_18_14_8_5_1_860 32 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 188 221 (accept_3_2 31 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 188 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 188 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 188 221 (Polychromatic418967fa.accept_9_2_8_5_1_228
  29 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 188 221 (accept_3_2 28
  188 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 188 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 188 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 221 (accept_3_2 25 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 188 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 188 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23
  188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 188 221 (accept_3_2 22
  188 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 188 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 188 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 221 (accept_3_2 19 188 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 188 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 188 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 221 (accept_3_2 16 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 188 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 221 (accept_3_2 13 188 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 188 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 221 (accept_3_2 10 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 8 188 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 221 (accept_3_2 7 188 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 188 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 221 (accept_3_2 4 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 188 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 221 (accept_3_2 1 188 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 221)))))))))))))))))))))))))))))))))) (allB_succ' 35 187 221 (Eq.refl Bool.true)
  (allA_of_3_0 35 187 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 186 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 186 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 221 (accept_3_2 34 186 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 186 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 186 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 186 221 (accept_3_2 31 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 186 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 186 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 221 (accept_3_2 28 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 221 (accept_3_2 25 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 186 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 221 (accept_3_2 22 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 186 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 221 (accept_3_2 19 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 221 (accept_3_2 16 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 221
  (Polychromatic418967fa.accept_16_14_10_13_1_2768 14 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 186 221 (accept_3_2 13 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 186 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 186 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 221 (accept_3_2 10 186 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 221 (Polychromatic418967fa.accept_11_9_10_1_1_581
  9 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 221 (accept_3_2 7 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 221 (Polychromatic418967fa.accept_19_6_15_12_1_6263 6 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 5 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 221 (accept_3_2 4 186 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 221 (accept_3_2 1 186 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  221)))))))))))))))))))))))))))))))))))) (allB_succ' 37 185 221 (Eq.refl Bool.true) (allA_succ_of_accept 36 185 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 185 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 185 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 221 (accept_3_2 34 185 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 185 221 (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 221 (accept_3_2 31 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 221 (Polychromatic418967fa.accept_20_10_5_1_1_4406 30 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 185 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 221 (accept_3_2 28 185 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 221
  (Polychromatic418967fa.accept_10_6_5_1_1_482 26 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 221 (accept_3_2 25 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 221 (accept_3_2 22 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 185
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 221 (accept_3_2 19 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 221 (Polychromatic418967fa.accept_27_18_23_5_1_5277 18 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 221 (accept_3_2 16 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 185 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 221
  (Polychromatic418967fa.accept_10_4_5_1_1_497 14 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 221 (accept_3_2 13 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 221 (Polychromatic418967fa.accept_23_11_1_14_1_6454 11 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 221 (accept_3_2 10 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 185 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 221 (accept_3_2 7 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 221 (Polychromatic418967fa.accept_16_5_9_13_1_3845 5 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 221 (accept_3_2 4 185 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 221 (Polychromatic418967fa.accept_20_3_5_1_1_4391 3 185 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 221 (accept_3_2 1 185 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  221))))))))))))))))))))))))))))))))))))) (allB_succ' 38 184 221 (Eq.refl Bool.true) (allA_of_3_0 38 184 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 183 221 (Eq.refl Bool.true) (allA_succ_of_accept 38 183 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 183 221 (accept_3_2 37 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 183 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 183 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 221 (accept_3_2 34 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 221 (accept_3_2 31 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 221 (accept_3_2 28 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 221 (Polychromatic418967fa.accept_21_6_15_11_1_5410 27 183 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 221 (accept_3_2 25 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 221 (Polychromatic418967fa.accept_15_8_3_11_1_849 23 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 221 (accept_3_2 22 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 183
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 221 (accept_3_2 19 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 221 (accept_3_2 16 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 221 (accept_3_2 13 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 221 (accept_3_2 10 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 221 (accept_3_2 7 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 221 (accept_3_2 4 183 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 221 (accept_3_2 1 183 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  221))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 182 221 (Eq.refl Bool.true) (allA_succ_of_gcd 39 182 221 13
  3 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 182
  221 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 182 221 (accept_3_2 37 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 182 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 182 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 182 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 182 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 182 221 (accept_3_2 34 182 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 182 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 182 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 182 221 (accept_3_2 31 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 182 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 182 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 29 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 221 (accept_3_2 28 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 182 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 221 13 2 14 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 221 (accept_3_2 25
  182 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 182 221
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 182 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 182 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 221 (accept_3_2 22 182 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 182 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 182 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 182 221 (Polychromatic418967fa.accept_12_8_2_5_1_844
  20 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 221 (accept_3_2 19
  182 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 221
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 182 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 182 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 221 (accept_3_2 16 182 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 182 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 221
  (Polychromatic418967fa.accept_25_14_7_21_1_13208 14 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 13 182 221 13 1 14 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 12 182 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 182 221 (accept_3_2 10 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  182 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 182 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 182 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 221 (accept_3_2 7 182 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 182 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 221
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 182 221 (accept_3_2 4 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  182 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 182 221 (Polychromatic418967fa.accept_21_2_14_11_1_7060 2 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 221 (accept_3_2 1 182 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 182 221)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 181 221
  (Eq.refl Bool.true) (allA_of_3_0 41 181 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 180 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 180 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 221 (accept_3_2 40 180 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 180 221 (Polychromatic418967fa.accept_16_7_4_13_1_1057 39 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 180 221
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 38 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 180 221 (accept_3_2 37 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 180 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 180 221 (Polychromatic418967fa.accept_19_16_9_12_1_4792 35 180 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 180 221 (accept_3_2 34 180 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 180 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 221
  (Polychromatic418967fa.accept_24_8_12_5_1_13207 32 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 180 221 (accept_3_2 31 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 180 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 180 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 180 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 221 (accept_3_2 28 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 180 221 (Polychromatic418967fa.accept_7_6_5_4_1_297
  27 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 221
  (Polychromatic418967fa.accept_21_5_12_11_1_5429 26 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 180 221 (accept_3_2 25 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 180 221 (Polychromatic418967fa.accept_16_8_4_13_1_1014 24 180 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 221 (accept_3_2 22 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 221
  (Polychromatic418967fa.accept_19_2_9_12_1_2237 21 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 180 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 180 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 221 (accept_3_2 19 180 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 180 221 (Polychromatic418967fa.accept_19_18_9_12_1_6153 18 180 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 221 (accept_3_2 16 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 180 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 180 221 (Polychromatic418967fa.accept_19_14_9_12_1_9113 14 180 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 221 (accept_3_2 13 180 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 221 (Polychromatic418967fa.accept_16_12_4_13_1_3827 12 180
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 221
  (Polychromatic418967fa.accept_22_11_4_1_1_13206 11 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 180 221 (accept_3_2 10 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 180 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 221 (accept_3_2 7 180 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 221
  (Polychromatic418967fa.accept_19_5_9_12_1_11778 5 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 221 (accept_3_2 4 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  180 221 (Polychromatic418967fa.accept_19_3_9_12_1_6253 3 180 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 180 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 180 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 221 (accept_3_2 1 180 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 180 221)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 179 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 42 179 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 221
  (Polychromatic418967fa.accept_24_17_11_5_1_7987 41 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 179 221 (accept_3_2 40 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 179 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 179 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 179 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 221 (accept_3_2 37 179 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 179 221
  (Polychromatic418967fa.accept_22_14_3_1_1_6769 36 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 179 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 179 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 221 (accept_3_2 34 179 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 179 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 221 (Polychromatic418967fa.accept_10_2_9_1_1_185
  32 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 221 (accept_3_2 31
  179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 179 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 179 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 221 (accept_3_2 28 179 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 179 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 221 (accept_3_2 25 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 221 (Polychromatic418967fa.accept_19_4_8_12_1_4757 23 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 221 (accept_3_2 22 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 179 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 221 (accept_3_2 19 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 221 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 221 (accept_3_2 16 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 179 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 221 (accept_3_2 13 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 221 (accept_3_2 10 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 221 (Polychromatic418967fa.accept_22_9_3_1_1_13184 9 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 221
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 221 (accept_3_2 7 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 221 (accept_3_2 4 179 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 179 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 221 (accept_3_2 1 179 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  221))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 178 221 (Eq.refl Bool.true) (allA_of_3_0 44 178 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 177 221 (Eq.refl Bool.true) (allA_succ_of_accept 44 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 221 (accept_3_2 43 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 177 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 177 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 221 (accept_3_2 40 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 221 (accept_3_2 37 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 177 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 221 (accept_3_2 34 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 221 (accept_3_2 31 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 221 (accept_3_2 28 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 221 (accept_3_2 25 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 221 (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 221 (accept_3_2 22 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 177 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 221 (accept_3_2 19 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 221 (Polychromatic418967fa.accept_19_18_6_12_1_6250 18 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 221 (accept_3_2 16 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 221 (accept_3_2 13 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 221 (accept_3_2 10 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 221 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 221 (accept_3_2 7 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 221 (accept_3_2 4 177 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 177 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 221 (accept_3_2 1 177 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  221))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 176 221 (Eq.refl Bool.true) (allA_succ_of_accept 45
  176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 176 221 (Polychromatic418967fa.accept_18_8_14_5_1_2778 44 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 176 221 (accept_3_2 43 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 176 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 176
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 176 221
  (Polychromatic418967fa.accept_21_20_8_11_1_5407 41 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 176 221 (accept_3_2 40 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 176 221 (accept_3_2 37 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 176 221
  (Polychromatic418967fa.accept_19_17_5_12_1_4753 36 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 176 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 221 (accept_3_2 34 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 176 221 (accept_3_2 31 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 176 221 (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 176 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 221 (accept_3_2 28 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 176 221 (accept_3_2 25 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 176 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 176 221 (Polychromatic418967fa.accept_19_4_5_12_1_3441 23 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 221 (accept_3_2 22 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 221
  (Polychromatic418967fa.accept_19_1_5_12_1_6249 20 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 176 221 (accept_3_2 19 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 176 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 221 (accept_3_2 16 176 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 221 (accept_3_2 13 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 221 (accept_3_2 10 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 221
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 8 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 221 (accept_3_2 7 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 221 (Polychromatic418967fa.accept_20_6_16_1_1_7262 6 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 176 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 221 (accept_3_2 4 176 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 221 (accept_3_2 1 176 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  221)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 175 221 (Eq.refl Bool.true) (allA_of_3_0 47 175 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 174 221 (Eq.refl Bool.true) (allA_succ_of_accept 47 174 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 174 221 (accept_3_2 46 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 174 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 174 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 221 (accept_3_2 43 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 174 221
  (Polychromatic418967fa.accept_21_20_6_11_1_2623 41 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 174 221 (accept_3_2 40 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 174 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 174 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 174 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 221 (accept_3_2 37 174 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 221 (Polychromatic418967fa.accept_15_6_9_11_1_858
  36 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 174 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 174 221 (accept_3_2 34 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 174 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 174 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 221 (accept_3_2 31 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 174 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 221 (accept_3_2 28 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 174 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 174 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 221 (accept_3_2 25 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 174 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 174 221 (accept_3_2 22 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 174 221 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 174 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 221 (accept_3_2 19 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 221 (Polychromatic418967fa.accept_21_18_6_11_1_7031 18 174 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 174 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 221 (accept_3_2 16 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 174 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 174 221 (Polychromatic418967fa.accept_21_14_6_11_1_7071 14 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 221 (accept_3_2 13 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 174 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 174 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 221 (accept_3_2 10 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  174 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 174 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 221 (accept_3_2 7 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 174 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 174 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 221 (accept_3_2 4 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  174 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 174 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 221 (accept_3_2 1 174 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 174 221)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 173 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 173 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 173 221
  (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 173 221 (accept_3_2 46 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 173 221 (Polychromatic418967fa.accept_25_20_23_21_1_7825 45 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 173 221 (accept_3_2 43 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 173 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 173 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 173 221 (accept_3_2 40 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 173 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 173 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 221 (accept_3_2 37 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 173 221 (accept_3_2 34 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 173 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 173 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 221 (accept_3_2 31 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 221 (accept_3_2 28 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 221 (accept_3_2 25 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 221 (accept_3_2 22 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 221 (accept_3_2 19 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 173 221 (accept_3_2 16 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 173 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 173 221 (Polychromatic418967fa.accept_18_14_11_5_1_7967 14 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 221 (accept_3_2 13 173 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 221
  (Polychromatic418967fa.accept_22_11_19_1_1_8415 11 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 173 221 (accept_3_2 10 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 173 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 173 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 221 (accept_3_2 7 173 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 221
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 221 (accept_3_2 4 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 173 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 221 (accept_3_2 1 173 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 221))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 172 221
  (Eq.refl Bool.true) (allA_of_3_0 50 172 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 171 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 50 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 221 (accept_3_2 49 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 171 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 221 (accept_3_2 46 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 221 (accept_3_2 43 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 171 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 221 (accept_3_2 40 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 221 (accept_3_2 37 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 221
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 221 (accept_3_2 34 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 221 (accept_3_2 31 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 221 (accept_3_2 28 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 221 (accept_3_2 25 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 221
  (Polychromatic418967fa.accept_27_23_9_5_1_13205 23 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 221 (accept_3_2 22 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 171 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 171 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 221 (accept_3_2 19 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 221 (accept_3_2 16 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 221 (accept_3_2 13 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 221 (Polychromatic418967fa.accept_18_12_9_5_1_2771 12 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 221
  (Polychromatic418967fa.accept_26_11_15_13_1_13204 11 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 221 (accept_3_2 10 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 171 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 171 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 221 (accept_3_2 7 171 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 221
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 221 (accept_3_2 4 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 171 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 221 (accept_3_2 1 171 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 221))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 170 221
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 170 221 17 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 170 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 170 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 170 221 (accept_3_2 49 170 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 170 221 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 170 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 47 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 170 221 (accept_3_2 46 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 170 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 170 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 44 170 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 170 221 (accept_3_2 43 170 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 170 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 170 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 170 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 170 221 (accept_3_2 40 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 170 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 221 (accept_3_2 37 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 170 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 170 221 17 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 170 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 221 (Polychromatic418967fa.accept_12_8_2_5_1_844
  32 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 221 (accept_3_2 31
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 30 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 170 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 170 221 (accept_3_2 28 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 221 (Polychromatic418967fa.accept_7_5_2_4_1_126
  26 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 221 (accept_3_2 25
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 24 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 221 (accept_3_2 22 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 170 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 170 221 (Polychromatic418967fa.accept_7_6_2_4_1_291
  20 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 221 (accept_3_2 19
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 221
  (Polychromatic418967fa.accept_23_18_9_14_1_13203 18 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 17 170 221 17 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 16 170 221 (accept_3_2 16 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 170 221 (Polychromatic418967fa.accept_16_14_10_13_1_2768 14
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 221 (accept_3_2 13
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 221 (accept_3_2 10 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 170 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 8
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 221 (accept_3_2 7 170
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 170 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 221 (accept_3_2 4 170 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 170 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 170 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2
  170 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 221 (accept_3_2 1 170
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 221))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 169 221 (Eq.refl Bool.true) (allA_of_3_0 53 169 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 54 168 221 (Eq.refl Bool.true) (allA_succ_of_accept 53 168 221 (Polychromatic418967fa.accept_9_8_6_5_1_513
  53 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 221 (accept_3_2 52
  168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 168 221
  (Polychromatic418967fa.accept_15_6_3_11_1_848 51 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 168 221 (Polychromatic418967fa.accept_23_4_7_14_1_13202 50 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 168 221 (accept_3_2 49 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 168 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 168 221 (accept_3_2 46 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 168 221 (Polychromatic418967fa.accept_19_7_16_12_1_10556 45 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 221 (accept_3_2 43 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 221 (Polychromatic418967fa.accept_19_4_16_12_1_485 42 168
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 168 221
  (Polychromatic418967fa.accept_23_18_7_14_1_13173 41 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 168 221 (accept_3_2 40 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 168 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 38 168 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 221 (accept_3_2 37 168 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 221 (Polychromatic418967fa.accept_15_6_3_11_1_848
  36 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 168 221 (accept_3_2 34 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 168 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 33 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 168 221 (Polychromatic418967fa.accept_19_13_16_12_1_6096 32 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 221 (accept_3_2 31 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 168 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 168 221 (accept_3_2 28 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 168 221 (Polychromatic418967fa.accept_16_11_8_13_1_3844 27 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 168 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 221 (accept_3_2 25 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 221
  (Polychromatic418967fa.accept_10_3_8_1_1_182 23 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 221 (accept_3_2 22 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 168 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 221 (accept_3_2 19 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 221 (Polychromatic418967fa.accept_20_18_8_1_1_10382 18 168 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 221 (accept_3_2 16 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 221 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 221 (Polychromatic418967fa.accept_15_14_3_11_1_850 14 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 221 (accept_3_2 13 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 168 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 221 (accept_3_2 10 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 221 (accept_3_2 7 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 168 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 221
  (Polychromatic418967fa.accept_16_5_8_13_1_2764 5 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 221 (accept_3_2 4 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 221 (accept_3_2 1 168 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 221)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 167 221
  (Eq.refl Bool.true) (allA_succ_of_accept 54 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 221
  (Polychromatic418967fa.accept_22_9_13_1_1_8400 53 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 221 (accept_3_2 52 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 221 (accept_3_2 49 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 221 (Polychromatic418967fa.accept_20_8_7_1_1_3024 48 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 221 (accept_3_2 46 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 221 (accept_3_2 43 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 221
  (Polychromatic418967fa.accept_16_9_7_13_1_4997 41 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 221 (accept_3_2 40 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 221 (accept_3_2 37 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 221 (accept_3_2 34 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 221 (accept_3_2 31 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 167 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 221
  (Polychromatic418967fa.accept_21_8_20_11_1_7025 29 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 167 221 (accept_3_2 28 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 167 221 (Polychromatic418967fa.accept_19_8_15_12_1_2240 27 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26
  167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 221 (accept_3_2 25
  167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 167 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 167 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 221 (accept_3_2 22 167 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 167 221 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 20 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 221 (accept_3_2 19 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 221 (accept_3_2 16 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 221 (Polychromatic418967fa.accept_20_15_7_1_1_5885 15 167 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 221 (accept_3_2 13 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 221 (Polychromatic418967fa.accept_20_11_7_1_1_8874 11 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 221 (accept_3_2 10 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 167 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 221
  (Polychromatic418967fa.accept_19_8_15_12_1_2240 8 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 221 (accept_3_2 7 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 221 (accept_3_2 4 167 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 167 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 221 (accept_3_2 1 167 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 166 221 (Eq.refl Bool.true) (allA_of_3_0 56
  166 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 165 221 (Eq.refl Bool.true) (allA_succ_of_accept 56
  165 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 165 221 (accept_3_2 55 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 165 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 165 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 165 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 165 221 (accept_3_2 52 165 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240
  51 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 50 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 165 221 (accept_3_2 49 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 165 221 (Polychromatic418967fa.accept_21_6_18_11_1_3960 48 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 221 (accept_3_2 46 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 221 (Polychromatic418967fa.accept_21_3_18_11_1_10061 45 165 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 221 (accept_3_2 43 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 165 221 (Polychromatic418967fa.accept_16_9_5_13_1_4972 41 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 221 (accept_3_2 40 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 165
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 221 (accept_3_2 37 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 221 (accept_3_2 34 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 221 (accept_3_2 31 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 165 221 (Polychromatic418967fa.accept_19_11_13_12_1_6259 30 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 221 (accept_3_2 28 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 165
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 221 (accept_3_2 25 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 221 (Polychromatic418967fa.accept_20_3_5_1_1_4391 23 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 221 (accept_3_2 22 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 221 (Polychromatic418967fa.accept_22_21_11_1_1_13201 21
  165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 221 (accept_3_2 19 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 221 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 221 (accept_3_2 16 165 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 221 (accept_3_2 13 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 165 221 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 221 (accept_3_2 10 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 165 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 221 (accept_3_2 7 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 221 (Polychromatic418967fa.accept_19_5_13_12_1_13154 5 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 221 (accept_3_2 4 165 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 165 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 221 (accept_3_2 1 165 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 164 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 164 221 (Polychromatic418967fa.accept_16_8_4_13_1_1014 56 164
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 164 221 (accept_3_2 55 164
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 164 221
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 54 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 164 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 164 221 (accept_3_2 52 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 164 221 (Polychromatic418967fa.accept_7_1_3_4_1_128
  50 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 221 (accept_3_2 49
  164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 164 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 164 221 (accept_3_2 46 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 164 221 (Polychromatic418967fa.accept_9_8_2_5_1_237
  44 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 221 (accept_3_2 43
  164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 221
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 164 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 221 (accept_3_2 40 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 221 (Polychromatic418967fa.accept_12_2_8_5_1_408
  38 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 221 (accept_3_2 37
  164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 164 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 221 (accept_3_2 34 164 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 221
  (Polychromatic418967fa.accept_23_9_3_14_1_6455 32 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 221 (accept_3_2 31 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 221 (accept_3_2 28 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 164 221 (accept_3_2 25 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 164 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 164 221 (Polychromatic418967fa.accept_16_7_4_13_1_1057 23 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 221 (accept_3_2 22 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 221 (accept_3_2 19 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 221 (accept_3_2 16 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 221 (accept_3_2 13 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 221 (Polychromatic418967fa.accept_20_11_4_1_1_4389 11 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 221 (accept_3_2 10 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 221 (accept_3_2 7 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 5 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 221 (accept_3_2 4 164 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 221
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 221 (accept_3_2 1 164 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 163 221 (Eq.refl Bool.true) (allA_of_3_0
  59 163 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 162 221 (Eq.refl Bool.true) (allA_succ_of_accept 59
  162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 162 221 (accept_3_2 58 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 162 221 (Polychromatic418967fa.accept_23_11_1_14_1_6454 57 162 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 221 (Polychromatic418967fa.accept_10_6_2_1_1_494
  56 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 221 (accept_3_2 55
  162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 221 (accept_3_2 52 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 162 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 221
  (Polychromatic418967fa.accept_23_4_1_14_1_13200 50 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 162 221 (accept_3_2 49 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 162 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 162 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 221 (accept_3_2 46 162 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 162 221 (Polychromatic418967fa.accept_7_3_1_4_1_121
  45 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 221
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 162 221 (accept_3_2 43 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 162 221 (Polychromatic418967fa.accept_22_20_8_1_1_6734 42 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 162 221 (Polychromatic418967fa.accept_19_3_10_12_1_6217 41 162
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 221 (accept_3_2 40 162
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 162 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 221 (accept_3_2 37 162 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 162 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 162 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 221 (accept_3_2 34 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 162 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 162 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 32 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 221 (accept_3_2 31 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 221 (Polychromatic418967fa.accept_19_11_10_12_1_2256 30
  162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 221
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 162 221 (accept_3_2 28 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 162 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 162 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 221 (accept_3_2 25 162 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 162 221 (accept_3_2 22 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 162 221 (Polychromatic418967fa.accept_16_5_2_13_1_1007 21 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 221 (Polychromatic418967fa.accept_22_20_8_1_1_6734 20 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 221 (accept_3_2 19 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 162
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 221 (accept_3_2 16 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 162 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 221 (accept_3_2 13 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 162 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 162 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 162 221 (accept_3_2 10 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  162 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 162 221 (Polychromatic418967fa.accept_15_8_12_11_1_1570 8 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 221 (accept_3_2 7 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 162 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 162 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 221 (accept_3_2 4 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  162 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 162 221 (Polychromatic418967fa.accept_19_2_10_12_1_3446 2 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 221 (accept_3_2 1 162 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 161 221 (Eq.refl Bool.true) (allA_succ_of_accept 60 161 221 (Polychromatic418967fa.accept_8_4_1_5_1_186
  60 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 161 221
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 161 221 (accept_3_2 58 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 161 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 161 221 (accept_3_2 55 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 161 221 (Polychromatic418967fa.accept_19_16_9_12_1_4792 54 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 221
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 53 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 161 221 (accept_3_2 52 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 161 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 50 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 221 (accept_3_2 49 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 47 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 221 (accept_3_2 46 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 45 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 44 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 221 (accept_3_2 43 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 221
  (Polychromatic418967fa.accept_16_9_1_13_1_1850 41 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 221 (accept_3_2 40 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 38 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 221 (accept_3_2 37 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 221
  (Polychromatic418967fa.accept_16_3_1_13_1_4968 35 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 221 (accept_3_2 34 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 221 (Polychromatic418967fa.accept_14_4_7_11_1_790 32 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 221 (accept_3_2 31 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 221 (accept_3_2 28 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 221 (Polychromatic418967fa.accept_21_6_14_11_1_10103 27 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 26 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 221 (accept_3_2 25 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837
  24 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 221
  (Polychromatic418967fa.accept_21_2_14_11_1_7060 23 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 161 221 (accept_3_2 22 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 161 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 221 (accept_3_2 19 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 221 (Polychromatic418967fa.accept_14_4_7_11_1_790
  18 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 221
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 221 (accept_3_2 16 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 221 (Polychromatic418967fa.accept_16_14_1_13_1_2754 14 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 221 (accept_3_2 13 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 221 (accept_3_2 10 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 221 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 221 (Polychromatic418967fa.accept_18_8_17_5_1_9273 8 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 221 (accept_3_2 7 161 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 221
  (Polychromatic418967fa.accept_16_5_1_13_1_1053 5 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 221 (accept_3_2 4 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 161 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 221 (accept_3_2 1 161 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 160
  221 (Eq.refl Bool.true) (allA_of_3_0 62 160 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 159 221
  (Eq.refl Bool.true) (allA_succ_of_accept 62 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 221 (accept_3_2 61 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 221 (Polychromatic418967fa.accept_16_12_15_13_1_3872 60
  159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 221
  (Polychromatic418967fa.accept_22_15_5_1_1_8441 59 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 221 (accept_3_2 58 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 221 (accept_3_2 55 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 221 (accept_3_2 52 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 221 (accept_3_2 49 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 47 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 221 (accept_3_2 46 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 221 (accept_3_2 43 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 221 (accept_3_2 40 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 221 (accept_3_2 37 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 35 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 221 (accept_3_2 34 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 33 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 221 (accept_3_2 31 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 221 (accept_3_2 28 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 221 (accept_3_2 25 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 24 159 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 221 (accept_3_2 22 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 221 (accept_3_2 19 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 17 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 221 (accept_3_2 16 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 221 (accept_3_2 13 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 221 (accept_3_2 10 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 221 (accept_3_2 7 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 221 (accept_3_2 4 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 159 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 221 (accept_3_2 1 159 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  158 221 (Eq.refl Bool.true) (allA_succ_of_accept 63 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 158 221
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 62 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 158 221 (accept_3_2 61 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 158 221 (Polychromatic418967fa.accept_26_8_2_13_1_9504 60 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 158 221 (accept_3_2 58 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 158 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 158 221 (accept_3_2 55 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 221 (Polychromatic418967fa.accept_19_16_6_12_1_11776 54 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 158 221 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 221 (accept_3_2 52 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 221 (accept_3_2 49 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 48 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 221 (accept_3_2 46 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 221 (accept_3_2 43 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 221 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 221 (accept_3_2 40 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 221
  (Polychromatic418967fa.accept_25_13_8_21_1_13199 38 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 158 221 (accept_3_2 37 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 158 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 158 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 221 (accept_3_2 34 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 32 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 221 (accept_3_2 31 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 221 (accept_3_2 28 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 221
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 158 221 (accept_3_2 25 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 158 221 (Polychromatic418967fa.accept_26_24_2_13_1_13198 24 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23
  158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 221 (accept_3_2 22
  158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 158 221 (Polychromatic418967fa.accept_12_8_2_5_1_844 20 158 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 221 (accept_3_2 19 158 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 158 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 221
  (Polychromatic418967fa.accept_16_1_14_13_1_3834 17 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 158 221 (accept_3_2 16 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 158 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 221 (Polychromatic418967fa.accept_19_14_6_12_1_13167 14
  158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 221 (accept_3_2 13
  158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 221
  (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 221 (accept_3_2 10 158 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 221
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 221 (accept_3_2 7 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 221 (Polychromatic418967fa.accept_23_6_20_14_1_8199 6 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 221 (accept_3_2 4 158 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 158 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 221
  (Polychromatic418967fa.accept_19_2_6_12_1_6270 2 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 221 (accept_3_2 1 158 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 157 221 (Eq.refl Bool.true)
  (allA_of_3_0 65 157 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 156 221 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 156 221 13 5 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 156 221 (accept_3_2 64 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 156 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 63 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 221 (accept_3_2 61 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 221 (Polychromatic418967fa.accept_9_6_3_5_1_240
  60 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 156 221
  (Polychromatic418967fa.accept_19_2_4_12_1_13084 59 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 156 221 (accept_3_2 58 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 156 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 56 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 221 (accept_3_2 55 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 221 (Polychromatic418967fa.accept_7_5_2_4_1_126
  54 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 156 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 221 13 4 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 156 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 221 (Polychromatic418967fa.accept_15_5_6_11_1_854
  50 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 221 (accept_3_2 49
  156 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 156 221 (accept_3_2 46 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 156 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 156 221 (accept_3_2 43 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 156 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 156 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 156 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 156 221 (accept_3_2 40 156 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 39 156 221 13 3 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 156 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 38 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 221 (accept_3_2 37 156 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 221 (Polychromatic418967fa.accept_11_3_2_1_1_994
  36 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 221 (accept_3_2 34 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 156 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 156 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 156 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 221 (accept_3_2 31 156 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 221 (Polychromatic418967fa.accept_19_11_4_12_1_6106 30 156
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 221 (accept_3_2 28 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 156 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 156 221 13 2 12 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 156 221 (accept_3_2 25 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 156 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 221 (Polychromatic418967fa.accept_14_9_2_11_1_780 23 156
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 221 (accept_3_2 22 156
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 221
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 156 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 221 (accept_3_2 19 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 156 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 156 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 17 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 221 (accept_3_2 16 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 156 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 156 221 13 1 12 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 156 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 221 (accept_3_2 10 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 8
  156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 221 (accept_3_2 7 156
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 221 (accept_3_2 4 156 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 156 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 221 (Polychromatic418967fa.accept_9_2_3_5_1_60 2
  156 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 221 (accept_3_2 1 156
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 155 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 66 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 155 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 155 221 (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 155
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 221 (accept_3_2 64 155
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 221
  (Polychromatic418967fa.accept_25_13_5_21_1_9645 63 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 221 (accept_3_2 61 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 155 221 (accept_3_2 58 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 155 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 155 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 221 (accept_3_2 55 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 53 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 221 (accept_3_2 52 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 221 (accept_3_2 49 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 155 221 (accept_3_2 46 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 155 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 155 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 44 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 221 (accept_3_2 43 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 155 221
  (Polychromatic418967fa.accept_21_20_8_11_1_5407 41 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 155 221 (accept_3_2 40 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 155 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 155 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 221 (accept_3_2 37 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 221 (Polychromatic418967fa.accept_10_6_5_1_1_482
  36 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 35 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 221 (accept_3_2 34 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 32 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 221 (accept_3_2 31 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 221 (accept_3_2 28 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 221 (Polychromatic418967fa.accept_20_7_15_1_1_13089 27 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 221 (accept_3_2 25 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 221 (accept_3_2 22 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 221 (Polychromatic418967fa.accept_21_20_8_11_1_5407 20 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 221 (accept_3_2 19 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 221 (accept_3_2 16 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 221 (accept_3_2 13 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 155 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 221
  (Polychromatic418967fa.accept_19_11_3_12_1_6138 11 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 221 (accept_3_2 10 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 155 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 221 (accept_3_2 7 155 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6
  155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 221 (accept_3_2 4 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 155 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 221 (accept_3_2 1 155 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 154 221 (Eq.refl Bool.true) (allA_of_3_0 68 154 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 153 221
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 153 221 17 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 153 221 (accept_3_2 67 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 153 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 153 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 153 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 221 (accept_3_2 64 153 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 221 (Polychromatic418967fa.accept_12_3_9_5_1_853
  63 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 62 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 221 (accept_3_2 61 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 221 (accept_3_2 58 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 153 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 221 (accept_3_2 55 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 221 (Polychromatic418967fa.accept_11_9_10_1_1_581 53 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 221 (accept_3_2 52 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 153 221 17 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 153 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 50
  153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 221 (accept_3_2 49
  153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 221
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 153 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 153 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 221 (accept_3_2 46 153 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 153 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44
  153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 221 (accept_3_2 43
  153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 221
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 221 (Polychromatic418967fa.accept_21_20_6_11_1_2623 41 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 221 (accept_3_2 40 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 221 (accept_3_2 37 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 153 221 17 2 9 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 153 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 221 (accept_3_2 31 153 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 29 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 221 (accept_3_2 28 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 221 (accept_3_2 25 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 221 (accept_3_2 22 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 221 (accept_3_2 19 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 221 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 153 221 17 1 9 13 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 153 221 (accept_3_2 16 153 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 221 (Polychromatic418967fa.accept_12_3_9_5_1_853
  15 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 221 (accept_3_2 13 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 221 (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 221 (accept_3_2 10 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 221 (accept_3_2 7 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 6 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 221 (accept_3_2 4 153 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 153 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 221 (accept_3_2 1 153 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 152 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 152 221 (Polychromatic418967fa.accept_16_4_8_13_1_1059 68 152
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 152 221 (accept_3_2 67 152
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 152 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 66 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 152 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 152 221 (accept_3_2 64 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 221 (Polychromatic418967fa.accept_7_6_5_4_1_297
  62 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 152 221 (accept_3_2 61
  152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 152 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 60 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 152 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 59 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 221 (accept_3_2 58 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 221 (Polychromatic418967fa.accept_9_2_8_5_1_228
  56 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 152 221 (accept_3_2 55
  152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 152 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 54 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 152 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 53 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 221 (accept_3_2 52 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 221 (Polychromatic418967fa.accept_7_1_5_4_1_134
  50 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 152 221 (accept_3_2 49
  152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 152 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 152 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 221 (accept_3_2 46 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 221 (Polychromatic418967fa.accept_7_2_5_4_1_115
  44 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 152 221 (accept_3_2 43
  152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 221
  (Polychromatic418967fa.accept_9_6_8_5_1_837 42 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 152 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 221 (accept_3_2 40 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 221 (Polychromatic418967fa.accept_9_2_8_5_1_228
  38 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 221 (accept_3_2 37
  152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 152 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 221 (accept_3_2 34 152 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 221
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 221 (accept_3_2 31 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 221 (accept_3_2 28 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 221
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 221 (accept_3_2 25 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 221 (accept_3_2 22 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 221 (accept_3_2 19 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 221 (Polychromatic418967fa.accept_21_18_5_11_1_7013 18 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 221 (Polychromatic418967fa.accept_18_17_8_5_1_2769 17 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 221 (accept_3_2 16 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 221 (accept_3_2 13 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 221 (accept_3_2 10 152 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 221 (accept_3_2 7 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 221 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 221 (accept_3_2 4 152 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 221 (accept_3_2 1 152 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 151 221 (Eq.refl Bool.true)
  (allA_of_3_0 71 151 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 150 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 150 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 221 (accept_3_2 70 150 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 150 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 221
  (Polychromatic418967fa.accept_16_4_6_13_1_1874 68 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 150 221 (accept_3_2 67 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 150 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 66 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 150 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 221 (accept_3_2 64 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 62 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 150 221 (accept_3_2 61 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 150 221 (Polychromatic418967fa.accept_19_3_17_12_1_6176 60 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 221 (accept_3_2 58 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 150 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 150 221 (accept_3_2 55 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 150 221 (Polychromatic418967fa.accept_20_14_10_1_1_13086 54 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 221 (accept_3_2 52 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 50 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 150 221 (accept_3_2 49 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 150 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 221 (accept_3_2 46 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 150 221 (Polychromatic418967fa.accept_20_5_10_1_1_11750 45 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 150 221 (accept_3_2 43 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 150 221 (Polychromatic418967fa.accept_22_20_18_1_1_13197 42 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 150 221 (accept_3_2 40 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 38 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 221 (accept_3_2 37 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 150 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 150 221 (accept_3_2 34 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 221 (Polychromatic418967fa.accept_18_15_6_5_1_3972 33 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 221
  (Polychromatic418967fa.accept_24_8_6_5_1_1399 32 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 221 (accept_3_2 31 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 150 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 150 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 221 (accept_3_2 28 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 150 221 (accept_3_2 25 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 150 221 (Polychromatic418967fa.accept_19_5_17_12_1_6120 24 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 221 (accept_3_2 22 150 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 221 (accept_3_2 19 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 150 221 (Polychromatic418967fa.accept_19_18_17_12_1_4764 18 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 221 (accept_3_2 16 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 221
  (Polychromatic418967fa.accept_19_14_17_12_1_6099 14 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 150 221 (accept_3_2 13 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 150 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 150 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 221 (accept_3_2 10 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 221 (Polychromatic418967fa.accept_16_9_6_13_1_3831
  9 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 221 (accept_3_2 7 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  150 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 150 221 (Polychromatic418967fa.accept_19_5_17_12_1_6120 5 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 221 (accept_3_2 4 150 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 150 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 150 221 (accept_3_2 1 150 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 149 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 149 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 149 221 (accept_3_2 70 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 149 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 69 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 68 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 221 (accept_3_2 67 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 149 221 (Polychromatic418967fa.accept_16_2_5_13_1_3842 66 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 65 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 221 (accept_3_2 64 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 221 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 221 (accept_3_2 61 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 221
  (Polychromatic418967fa.accept_21_17_2_11_1_8656 59 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 149 221 (accept_3_2 58 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 149 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 57 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 221
  (Polychromatic418967fa.accept_16_8_5_13_1_1021 56 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 221 (accept_3_2 55 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 221 (Polychromatic418967fa.accept_19_15_16_12_1_4779 53 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 221 (accept_3_2 52 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 51 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 221
  (Polychromatic418967fa.accept_16_2_5_13_1_3842 50 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 221 (accept_3_2 49 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 221 (accept_3_2 46 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 221
  (Polychromatic418967fa.accept_14_2_9_11_1_3054 44 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 221 (accept_3_2 43 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 221 (accept_3_2 40 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 221 (Polychromatic418967fa.accept_28_11_9_25_1_13196 39 149 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 221
  (Polychromatic418967fa.accept_10_8_9_1_1_189 38 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 221 (accept_3_2 37 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 221 (Polychromatic418967fa.accept_25_11_24_21_1_4074 36 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 221 (accept_3_2 34 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 149 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 221
  (Polychromatic418967fa.accept_10_2_9_1_1_185 32 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 221 (accept_3_2 31 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 221 (Polychromatic418967fa.accept_14_2_9_11_1_3054 30 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 221 (accept_3_2 28 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 149 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 26 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 221 (accept_3_2 25 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 221 (Polychromatic418967fa.accept_16_8_5_13_1_1021 24 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 221 (Polychromatic418967fa.accept_19_4_16_12_1_485 23 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 221 (accept_3_2 22 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 221 (Polychromatic418967fa.accept_22_21_17_1_1_9986 21 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 221 (accept_3_2 19 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 221 (Polychromatic418967fa.accept_16_1_5_13_1_1025 17 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 221 (accept_3_2 16 149 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 221
  (Polychromatic418967fa.accept_19_14_16_12_1_13098 14 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 149 221 (accept_3_2 13 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 221 (Polychromatic418967fa.accept_25_11_24_21_1_4074 11
  149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 221 (accept_3_2 10
  149 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 221
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 149 221 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 221 (accept_3_2 7 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 149 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 149 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 5
  149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 221 (accept_3_2 4 149
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 221
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 149 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 149 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 221 (accept_3_2 1 149 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 149 221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  148 221 (Eq.refl Bool.true) (allA_of_3_0 74 148 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 147 221
  (Eq.refl Bool.true) (allA_succ_of_accept 74 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 221 (accept_3_2 73 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 221 (Polychromatic418967fa.accept_16_8_3_13_1_7295 72 147
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 71 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 221 (accept_3_2 70 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 69 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 221 (accept_3_2 67 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 221 (accept_3_2 64 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 221 (accept_3_2 61 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 221
  (Polychromatic418967fa.accept_14_3_7_11_1_765 59 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 221 (accept_3_2 58 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 57 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 221 (accept_3_2 55 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 221 (accept_3_2 52 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 221 (accept_3_2 49 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 221 (Polychromatic418967fa.accept_19_10_14_12_1_4795 48 147 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 221 (accept_3_2 46 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 221 (accept_3_2 43 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 221
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 221 (accept_3_2 40 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 221 (Polychromatic418967fa.accept_29_10_2_18_1_13195 39 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 221 (accept_3_2 37 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 36 147
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 221 (accept_3_2 34 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 221 (accept_3_2 31 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 221 (accept_3_2 28 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 221 (Polychromatic418967fa.accept_22_5_15_1_1_5113 27 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 221 (accept_3_2 25 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 221
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 23 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 147 221 (accept_3_2 22 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 147 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 147 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 221 (accept_3_2 19 147 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 221 (accept_3_2 16 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 221 (accept_3_2 13 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 221 (Polychromatic418967fa.accept_22_12_15_1_1_13194 12 147 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 221 (accept_3_2 10 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 9 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 221 (accept_3_2 7 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 221
  (Polychromatic418967fa.accept_22_5_15_1_1_5113 5 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 221 (accept_3_2 4 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 221 (Polychromatic418967fa.accept_14_3_7_11_1_765 3 147 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 221 (accept_3_2 1 147 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 76 146 221 (Eq.refl Bool.true) (allA_succ_of_accept 75 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50
  75 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 146 221
  (Polychromatic418967fa.accept_20_14_6_1_1_3023 74 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 146 221 (accept_3_2 73 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 146 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 146 221 (accept_3_2 70 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 221 (accept_3_2 67 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 221 (accept_3_2 64 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 62 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 221 (accept_3_2 61 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 221 (accept_3_2 58 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 56 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 221 (accept_3_2 55 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 221 (accept_3_2 52 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 221
  (Polychromatic418967fa.accept_21_8_20_11_1_7025 50 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 146 221 (accept_3_2 49 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 146 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 48 146 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 221 (accept_3_2 46 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45
  146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 221 (accept_3_2 43 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 221 (Polychromatic418967fa.accept_19_3_13_12_1_10525 41 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 221 (accept_3_2 40 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 221 (accept_3_2 37 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 221 (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 221 (accept_3_2 34 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 221 (accept_3_2 31 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 221 (Polychromatic418967fa.accept_21_8_20_11_1_7025 29 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 221 (accept_3_2 28 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 221 (accept_3_2 25 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 221 (accept_3_2 22 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 20 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 221 (accept_3_2 19 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 221 (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 221 (accept_3_2 16 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 221
  (Polychromatic418967fa.accept_19_14_13_12_1_2259 14 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 146 221 (accept_3_2 13 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 146 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 146 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 221 (accept_3_2 10 146 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 221 (accept_3_2 7 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 221 (accept_3_2 4 146 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 146 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 221 (accept_3_2 1 146 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 145 221 (Eq.refl
  Bool.true) (allA_of_3_0 77 145 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 144 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 144 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 144 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 144 221 (accept_3_2 76 144 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 144 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 75 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 221
  (Polychromatic418967fa.accept_22_8_12_1_1_13175 74 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 144 221 (accept_3_2 73 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 144 221 (Polychromatic418967fa.accept_21_9_18_11_1_8644 72 144 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 144 221
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 71 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 144 221 (accept_3_2 70 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 144 221 (Polychromatic418967fa.accept_21_6_18_11_1_3960 69 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 144 221 (Polychromatic418967fa.accept_21_5_18_11_1_7041 68 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 221 (accept_3_2 67 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 66 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 144 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 65 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 144 221 (accept_3_2 64 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 144 221 (Polychromatic418967fa.accept_14_7_4_11_1_3038 63 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 144 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 62 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 221 (accept_3_2 61 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 221 (Polychromatic418967fa.accept_19_3_11_12_1_9102 60 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 144 221
  (Polychromatic418967fa.accept_22_15_12_1_1_13193 59 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 144 221 (accept_3_2 58 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 144 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 144 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 221 (Polychromatic418967fa.accept_19_18_11_12_1_6163 56
  144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 221 (accept_3_2 55
  144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 221
  (Polychromatic418967fa.accept_21_12_18_11_1_10051 54 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 221 (Polychromatic418967fa.accept_22_9_12_1_1_13192 53 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 221 (accept_3_2 52 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 51 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 221
  (Polychromatic418967fa.accept_14_8_4_11_1_3035 50 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 221 (accept_3_2 49 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 221 (Polychromatic418967fa.accept_19_10_11_12_1_6114 48 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 47 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 221 (accept_3_2 46 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 221
  (Polychromatic418967fa.accept_23_21_6_14_1_13191 44 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 144 221 (accept_3_2 43 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 144 221 (Polychromatic418967fa.accept_19_4_11_12_1_13189 42 144 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 221
  (Polychromatic418967fa.accept_19_3_11_12_1_9102 41 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 144 221 (accept_3_2 40 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 144 221 (Polychromatic418967fa.accept_19_1_11_12_1_6112 39 144 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 221
  (Polychromatic418967fa.accept_22_16_12_1_1_13174 38 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 144 221 (accept_3_2 37 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 144 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 36 144 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 35 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 221 (accept_3_2 34 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 221
  (Polychromatic418967fa.accept_21_12_18_11_1_10051 33 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 144 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 221 (accept_3_2 31 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 221 (Polychromatic418967fa.accept_20_10_4_1_1_8840 30 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 221
  (Polychromatic418967fa.accept_14_1_4_11_1_3036 29 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 221 (accept_3_2 28 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 144 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 144 221 (Polychromatic418967fa.accept_19_7_11_12_1_13190 26 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 221 (accept_3_2 25 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 221 (Polychromatic418967fa.accept_19_5_11_12_1_11765 24
  144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 221
  (Polychromatic418967fa.accept_19_4_11_12_1_13189 23 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 144 221 (accept_3_2 22 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 144 221 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 144 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 221 (Polychromatic418967fa.accept_15_5_9_11_1_4398 20 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 221 (accept_3_2 19 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 221
  (Polychromatic418967fa.accept_19_18_11_12_1_6163 18 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 221 (accept_3_2 16 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 221 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 144
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 221
  (Polychromatic418967fa.accept_21_14_18_11_1_3961 14 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 221 (accept_3_2 13 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 144 221 (Polychromatic418967fa.accept_21_12_18_11_1_10051 12 144 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 221
  (Polychromatic418967fa.accept_20_11_4_1_1_4389 11 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 221 (accept_3_2 10 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  144 221 (Polychromatic418967fa.accept_21_9_18_11_1_8644 9 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 144 221 (Polychromatic418967fa.accept_14_8_4_11_1_3035 8 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 221 (accept_3_2 7 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 6 144 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 221
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 221 (accept_3_2 4 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  144 221 (Polychromatic418967fa.accept_19_3_11_12_1_9102 3 144 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 144 221 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 221 (accept_3_2 1 144 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 143 221 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 143 221 13 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 143 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 221 (accept_3_2 76 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 143 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 75 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 74 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 143 221 (accept_3_2 73 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 143 221 (Polychromatic418967fa.accept_10_2_3_1_1_481 72 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 143 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 71 143 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 221 (accept_3_2 70 143 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 221
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 68 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 221 (accept_3_2 67 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 143 221 13 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 143 221 (accept_3_2 64 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 143 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 63 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 221 (accept_3_2 61 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 221 (Polychromatic418967fa.accept_9_6_8_5_1_837
  60 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 221
  (Polychromatic418967fa.accept_19_2_10_12_1_3446 59 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 143 221 (accept_3_2 58 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 143 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 221 (accept_3_2 55 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 221
  (Polychromatic418967fa.accept_20_13_3_1_1_3065 53 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 143 221 13 4 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 143 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 51 143 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50
  143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 221 (accept_3_2 49
  143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 143 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 221 (accept_3_2 46 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 143 221 (Polychromatic418967fa.accept_20_5_3_1_1_10415 45 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 221
  (Polychromatic418967fa.accept_16_12_15_13_1_3872 44 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 221 (accept_3_2 43 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 221 (accept_3_2 40 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 143 221 13 3 11 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 143 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 221 (accept_3_2 37 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 221 (accept_3_2 34 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 33 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 221
  (Polychromatic418967fa.accept_10_2_3_1_1_481 32 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 221 (accept_3_2 31 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 143 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 221 (accept_3_2 28 143 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 143 221 13 2 11 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 143 221 (accept_3_2 25 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 221 (Polychromatic418967fa.accept_9_6_8_5_1_837
  24 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 221
  (Polychromatic418967fa.accept_21_2_17_11_1_7037 23 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 143 221 (accept_3_2 22 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 143 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 221 (accept_3_2 19 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 221
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 17 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 221 (accept_3_2 16 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 143 221 13 1 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 143 221
  (Polychromatic418967fa.accept_9_3_8_5_1_65 12 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 221 (accept_3_2 10 143 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 143 221 (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 221 (accept_3_2 7 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 221 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 221 (accept_3_2 4 143 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 143 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 221 (accept_3_2 1 143 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 142 221 (Eq.refl
  Bool.true) (allA_of_3_0 80 142 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 141 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 80 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 141 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 221 (accept_3_2 79 141 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 141 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 221
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 77 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 221 (accept_3_2 76 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 75 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 221 (accept_3_2 73 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 221 (Polychromatic418967fa.accept_19_15_8_12_1_1286 72 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 71 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 221 (accept_3_2 70 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 221 (accept_3_2 67 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 65 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 221 (accept_3_2 64 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 221 (accept_3_2 61 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 60 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 221 (accept_3_2 58 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 57 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 221 (accept_3_2 55 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 53 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 221 (accept_3_2 52 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 51 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 221 (accept_3_2 49 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 221 (accept_3_2 46 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 221 (accept_3_2 43 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 42 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 221
  (Polychromatic418967fa.accept_24_17_21_5_1_11439 41 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 141 221 (accept_3_2 40 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 141 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 141 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 221 (accept_3_2 37 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 221
  (Polychromatic418967fa.accept_22_14_9_1_1_13188 36 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 221 (accept_3_2 34 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 221 (accept_3_2 31 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 221 (accept_3_2 28 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 27 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 221 (accept_3_2 25 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 221 (Polychromatic418967fa.accept_19_4_8_12_1_4757 23 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 221 (accept_3_2 22 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 221 (accept_3_2 19 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 221 (Polychromatic418967fa.accept_14_4_1_11_1_5026 18 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 221 (accept_3_2 16 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 15 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 221 (accept_3_2 13 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 221 (accept_3_2 10 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 221 (accept_3_2 7 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 221 (Polychromatic418967fa.accept_18_6_15_5_1_6563 6 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 221 (accept_3_2 4 141 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 141 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 221
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 221 (accept_3_2 1 141 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 140 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 140 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 140 221
  (Polychromatic418967fa.accept_18_8_14_5_1_2778 80 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 140 221 (accept_3_2 79 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 140 221 (Polychromatic418967fa.accept_22_12_8_1_1_5108 78 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 140 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 140 221 (accept_3_2 76 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 140 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 140 221 (accept_3_2 73 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 140 221 (Polychromatic418967fa.accept_16_8_12_13_1_3851 72 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 140 221 (Polychromatic418967fa.accept_19_14_7_12_1_7732 71 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 140 221 (accept_3_2 70 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 68 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 140 221 (accept_3_2 67 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 66 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 140 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 65 140 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 140 221 (accept_3_2 64 140 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 62 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 140 221 (accept_3_2 61 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 140 221 (Polychromatic418967fa.accept_19_3_7_12_1_9105 60 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 140 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 140 221 (accept_3_2 58 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 140 221
  (Polychromatic418967fa.accept_16_8_12_13_1_3851 56 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 140 221 (accept_3_2 55 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 140 221 (Polychromatic418967fa.accept_15_9_5_11_1_5416 54 140 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 140
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 221 (accept_3_2 52 140
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 140 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 140 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 50 140 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 140 221 (accept_3_2 49 140 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 140 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 47 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 140 221 (accept_3_2 46 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 140 221 (Polychromatic418967fa.accept_18_8_14_5_1_2778 44 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 140 221 (accept_3_2 43 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 140 221 (Polychromatic418967fa.accept_16_10_12_13_1_4950 42
  140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 221
  (Polychromatic418967fa.accept_8_1_4_5_1_48 41 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 140 221 (accept_3_2 40 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 140 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 38 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 221 (accept_3_2 37 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 140 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 140
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 140 221
  (Polychromatic418967fa.accept_19_16_7_12_1_6252 35 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 140 221 (accept_3_2 34 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 140 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 140
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 221 (accept_3_2 31 140
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 221
  (Polychromatic418967fa.accept_19_11_7_12_1_4770 30 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 29 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 221 (accept_3_2 28 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 221
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 221 (accept_3_2 25 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 221 (Polychromatic418967fa.accept_15_9_5_11_1_5416 24 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 221 (Polychromatic418967fa.accept_15_8_5_11_1_2358 23 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 221 (accept_3_2 22 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 221
  (Polychromatic418967fa.accept_16_4_12_13_1_990 20 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 221 (accept_3_2 19 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 221 (Polychromatic418967fa.accept_19_18_7_12_1_6148 18 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 17 140 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 221 (accept_3_2 16 140 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 14 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 140 221 (accept_3_2 13 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 140 221 (Polychromatic418967fa.accept_21_12_14_11_1_3921 12 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 221 (Polychromatic418967fa.accept_18_11_14_5_1_3951 11 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 221 (accept_3_2 10 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9
  140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 140 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 8 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 140 221 (accept_3_2 7 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  140 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 140 221 (Polychromatic418967fa.accept_19_5_7_12_1_2252 5 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 221 (accept_3_2 4 140 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 2 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 221 (accept_3_2 1 140 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 139 221 (Eq.refl
  Bool.true) (allA_of_3_0 83 139 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 138 221 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 138 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 138 221 (accept_3_2 82 138 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 138 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 81 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 80 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 138 221 (accept_3_2 79 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 138 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 78 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 138 221 (Polychromatic418967fa.accept_19_1_5_12_1_6249 77 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 221 (accept_3_2 76 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 138 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 74 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 221 (accept_3_2 73 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 138 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 221 (accept_3_2 70 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 221
  (Polychromatic418967fa.accept_15_8_3_11_1_849 68 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 138 221 (accept_3_2 67 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 138 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 66 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 221 (accept_3_2 64 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 221 (accept_3_2 61 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 138 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 221 (accept_3_2 58 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 221 (accept_3_2 55 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 138 221 (Polychromatic418967fa.accept_19_16_5_12_1_6142 54 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 53 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 221 (accept_3_2 52 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 221 (accept_3_2 49 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 221 (accept_3_2 46 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 221 (Polychromatic418967fa.accept_18_9_12_5_1_864 45 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 138 221 (accept_3_2 43 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 138 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 138 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 221 (accept_3_2 40 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 221 (accept_3_2 37 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 221 (accept_3_2 34 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 221
  (Polychromatic418967fa.accept_19_13_5_12_1_6107 32 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 138 221 (accept_3_2 31 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 138 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 138 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 138 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 221 (accept_3_2 28 138 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27
  138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 221 (accept_3_2 25 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 221 (accept_3_2 22 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 221 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 221 (accept_3_2 19 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 221 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 221 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 221 (accept_3_2 16 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 221
  (Polychromatic418967fa.accept_15_14_3_11_1_850 14 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 221 (accept_3_2 13 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 221 (Polychromatic418967fa.accept_16_12_10_13_1_1042 12 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 221 (accept_3_2 10 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 221 (accept_3_2 7 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 221 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 221 (accept_3_2 4 138 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 221
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 221 (accept_3_2 1 138 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 137 221
  (Eq.refl Bool.true) (allA_succ_of_accept 84 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 221
  (Polychromatic418967fa.accept_11_6_5_1_1_586 83 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 221 (accept_3_2 82 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 221 (Polychromatic418967fa.accept_15_6_2_11_1_325 81 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 80 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 221 (accept_3_2 79 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 221
  (Polychromatic418967fa.accept_19_1_4_12_1_6275 77 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 137 221 (accept_3_2 76 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 75 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 137 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 74 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 221 (accept_3_2 73 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 72 137
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 71 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 137 221 (accept_3_2 70 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 69 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 68 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 221 (accept_3_2 67 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 221 (accept_3_2 64 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 221 (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 62 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 221 (accept_3_2 61 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 221
  (Polychromatic418967fa.accept_19_2_4_12_1_13084 59 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 137 221 (accept_3_2 58 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 57 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 221 (Polychromatic418967fa.accept_10_6_7_1_1_1297 56 137
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 221 (accept_3_2 55 137
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 221
  (Polychromatic418967fa.accept_10_4_7_1_1_471 54 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 221 (accept_3_2 52 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 51 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 221 (Polychromatic418967fa.accept_11_6_5_1_1_586
  50 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 221 (accept_3_2 49
  137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 221
  (Polychromatic418967fa.accept_9_3_2_5_1_234 48 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 137 221 (Polychromatic418967fa.accept_22_3_5_1_1_13187 47 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 221 (accept_3_2 46 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 137 221 (Polychromatic418967fa.accept_19_7_4_12_1_4769 45 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 221
  (Polychromatic418967fa.accept_8_4_1_5_1_186 44 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 221 (accept_3_2 43 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 221 (Polychromatic418967fa.accept_23_18_22_14_1_13186 41 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 221 (accept_3_2 40 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 137 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 221
  (Polychromatic418967fa.accept_16_6_9_13_1_2751 38 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 221 (accept_3_2 37 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 221 (accept_3_2 34 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 33 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 221
  (Polychromatic418967fa.accept_18_14_11_5_1_7967 32 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 137 221 (accept_3_2 31 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 221 (Polychromatic418967fa.accept_31_29_13_4_1_13185 29
  137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 221 (accept_3_2 28
  137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 221
  (Polychromatic418967fa.accept_19_8_4_12_1_4768 27 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 221 (accept_3_2 25 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 221
  (Polychromatic418967fa.accept_16_7_9_13_1_4948 23 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 221 (accept_3_2 22 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 20 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 221 (accept_3_2 19 137 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 221 (Polychromatic418967fa.accept_20_18_17_1_1_10388 18 137 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 221 (accept_3_2 16 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 221 (Polychromatic418967fa.accept_10_4_7_1_1_471 14 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 221 (accept_3_2 13 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 137 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 221
  (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 137 221 (accept_3_2 10 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 137 221 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 137 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 137 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 221 (accept_3_2 7 137 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 6
  137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 221
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 221 (accept_3_2 4 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 137 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 221 (Polychromatic418967fa.accept_19_2_4_12_1_13084 2 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 221 (accept_3_2 1 137 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 137
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 136 221
  (Eq.refl Bool.true) (allA_of_3_0 86 136 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 135 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 86 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 221 (accept_3_2 85 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 84 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 83 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 221 (accept_3_2 82 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 81 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 221 (accept_3_2 79 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 221
  (Polychromatic418967fa.accept_19_1_2_12_1_7725 77 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 221 (accept_3_2 76 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 221 (accept_3_2 73 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 221 (Polychromatic418967fa.accept_14_2_9_11_1_3054 72 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 221
  (Polychromatic418967fa.accept_19_14_2_12_1_13164 71 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 135 221 (accept_3_2 70 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 135 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 135 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 221 (accept_3_2 67 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66
  135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 221
  (Polychromatic418967fa.accept_20_5_15_1_1_7278 65 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 221 (accept_3_2 64 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 221 (Polychromatic418967fa.accept_19_6_2_12_1_6136 63 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 221 (accept_3_2 61 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 221 (Polychromatic418967fa.accept_19_3_2_12_1_13118 60 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 59 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 221 (accept_3_2 58 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 221 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 221 (accept_3_2 55 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 221
  (Polychromatic418967fa.accept_22_9_3_1_1_13184 53 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 221 (accept_3_2 52 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 221 (Polychromatic418967fa.accept_18_15_9_5_1_3934 51 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 221 (accept_3_2 49 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 221 (accept_3_2 46 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 45 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 221 (accept_3_2 43 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 221 (accept_3_2 40 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 38 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 221 (accept_3_2 37 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 221
  (Polychromatic418967fa.accept_11_2_3_1_1_244 35 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 221 (accept_3_2 34 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 221 (accept_3_2 31 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 221
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 221 (accept_3_2 28 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 26 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 221 (accept_3_2 25 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 221
  (Polychromatic418967fa.accept_19_4_2_12_1_10527 23 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 135 221 (accept_3_2 22 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 135 221 (Polychromatic418967fa.accept_12_9_3_5_1_423 21 135 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 221 (accept_3_2 19 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18
  135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 221
  (Polychromatic418967fa.accept_19_17_2_12_1_4751 17 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 221 (accept_3_2 16 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 135 221 (Polychromatic418967fa.accept_18_15_9_5_1_3934 15 135 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 221 (accept_3_2 13 135 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 221 (Polychromatic418967fa.accept_7_5_2_4_1_126
  12 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 221
  (Polychromatic418967fa.accept_22_11_3_1_1_3481 11 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 221 (accept_3_2 10 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 221 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 221 (accept_3_2 7 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 221 (accept_3_2 4 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 221 (Polychromatic418967fa.accept_19_3_2_12_1_13118 3 135 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 221 (accept_3_2 1 135 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 134 221
  (Eq.refl Bool.true) (allA_succ_of_accept 87 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 134 221
  (Polychromatic418967fa.accept_18_14_8_5_1_860 86 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 134 221 (accept_3_2 85 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 134 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 134 221 (accept_3_2 82 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 134 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 80 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 134 221 (accept_3_2 79 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 134 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 134 221 (Polychromatic418967fa.accept_10_7_4_1_1_1319 77 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 134 221 (accept_3_2 76 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 134 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 74 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 134 221 (accept_3_2 73 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 134 221 (Polychromatic418967fa.accept_15_12_14_11_1_4375 72 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 221 (accept_3_2 70 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 134 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 68 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 221 (accept_3_2 67 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 221 (accept_3_2 64 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 221
  (Polychromatic418967fa.accept_19_5_1_12_1_6102 62 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 221 (accept_3_2 61 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 59 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 221 (accept_3_2 58 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 221 (accept_3_2 55 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 221 (Polychromatic418967fa.accept_18_17_8_5_1_2769 53 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 221 (accept_3_2 52 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 134 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 221
  (Polychromatic418967fa.accept_18_14_8_5_1_860 50 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 221 (accept_3_2 49 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 221 (accept_3_2 46 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 44 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 221 (accept_3_2 43 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 221 (Polychromatic418967fa.accept_16_9_6_13_1_3831 41 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 221 (accept_3_2 40 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 134 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 221
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 221 (accept_3_2 37 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 221 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 35 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 221 (accept_3_2 34 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 221
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 221 (accept_3_2 31 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 221 (accept_3_2 28 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 221
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 221 (accept_3_2 25 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 23 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 221 (accept_3_2 22 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 221 (accept_3_2 19 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 221 (Polychromatic418967fa.accept_14_4_8_11_1_794 18 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 221 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 221 (accept_3_2 16 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 221
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 221 (accept_3_2 13 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 221 (accept_3_2 10 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 221
  (Polychromatic418967fa.accept_12_8_2_5_1_844 8 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 221 (accept_3_2 7 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 221 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 221 (accept_3_2 4 134 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 134 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 221 (accept_3_2 1 134 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 133 221
  (Eq.refl Bool.true) (allA_of_3_0 89 133 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 132 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 89 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 132 221 (accept_3_2 88 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 86 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 132 221 (accept_3_2 85 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 132 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 84 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 132 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 83 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 221 (accept_3_2 82 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 81 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 80 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 132 221 (accept_3_2 79 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 132 221 (Polychromatic418967fa.accept_21_15_6_11_1_10126 78 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 221 (Polychromatic418967fa.accept_19_1_18_12_1_7755 77 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 221 (accept_3_2 76 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117
  75 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 74 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 132 221 (accept_3_2 73 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 132 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 71 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 221 (accept_3_2 70 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 221 (Polychromatic418967fa.accept_10_9_2_1_1_840 69 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 68 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 132 221 (accept_3_2 67 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 65 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 221 (accept_3_2 64 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 221 (Polychromatic418967fa.accept_10_3_2_1_1_839 63 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 221
  (Polychromatic418967fa.accept_9_8_6_5_1_513 62 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 132 221 (accept_3_2 61 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 132 221 (Polychromatic418967fa.accept_16_12_4_13_1_3827 60 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 221 (accept_3_2 58 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 57 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 221 (accept_3_2 55 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 221 (accept_3_2 52 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 221
  (Polychromatic418967fa.accept_23_4_17_14_1_13127 50 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 132 221 (accept_3_2 49 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 132 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 132 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 221 (accept_3_2 46 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45
  132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 221 (accept_3_2 43 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 221 (Polychromatic418967fa.accept_24_18_12_5_1_13102 42 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 221 (Polychromatic418967fa.accept_8_1_4_5_1_48 41 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 221 (accept_3_2 40 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 221 (accept_3_2 37 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 221 (accept_3_2 34 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 221
  (Polychromatic418967fa.accept_19_13_18_12_1_3428 32 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 132 221 (accept_3_2 31 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 132 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 29 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 221 (accept_3_2 28 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 221
  (Polychromatic418967fa.accept_23_4_17_14_1_13127 27 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 221 (accept_3_2 25 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 132 221 (accept_3_2 22 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 132 221 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 132 221 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 221 (accept_3_2 19 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 221 (Polychromatic418967fa.accept_21_18_6_11_1_7031 18 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 221 (accept_3_2 16 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 132 221 (Polychromatic418967fa.accept_18_15_6_5_1_3972 15 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 132 221 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 221 (accept_3_2 13 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 132 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 221
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 221 (accept_3_2 10 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 132 221 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 221 (accept_3_2 7 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 221 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 132 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 132 221 (accept_3_2 4 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  132 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 132 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 221 (accept_3_2 1 132 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 131 221
  (Eq.refl Bool.true) (allA_succ_of_accept 90 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 90 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 221
  (Polychromatic418967fa.accept_24_17_11_5_1_7987 89 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 131 221 (accept_3_2 88 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 131 221 (Polychromatic418967fa.accept_20_7_11_1_1_5840 87 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 86 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 221 (accept_3_2 85 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 221
  (Polychromatic418967fa.accept_20_4_11_1_1_10409 84 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 83 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 221 (accept_3_2 82 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 221 (Polychromatic418967fa.accept_16_1_3_13_1_2785 81 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 221
  (Polychromatic418967fa.accept_21_17_5_11_1_7028 80 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 131 221 (accept_3_2 79 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 221 (Polychromatic418967fa.accept_20_17_11_1_1_8865 77 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 221 (accept_3_2 76 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 221
  (Polychromatic418967fa.accept_11_9_10_1_1_581 75 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 74 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 221 (accept_3_2 73 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 72 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 221 (Polychromatic418967fa.accept_7_1_5_4_1_134
  71 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 221 (accept_3_2 70
  131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 69 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 131 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 68 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 221 (accept_3_2 67 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115
  65 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 221 (accept_3_2 64
  131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 221
  (Polychromatic418967fa.accept_16_15_3_13_1_2818 63 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 62 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 221 (accept_3_2 61 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 221 (Polychromatic418967fa.accept_19_3_17_12_1_6176 60 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 221
  (Polychromatic418967fa.accept_19_2_17_12_1_6097 59 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 131 221 (accept_3_2 58 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 131 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 221 (Polychromatic418967fa.accept_16_8_3_13_1_7295 56 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 221 (accept_3_2 55 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2
  54 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 221
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 221 (accept_3_2 52 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 50 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 221 (accept_3_2 49 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 221
  (Polychromatic418967fa.accept_16_15_3_13_1_2818 47 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 131 221 (accept_3_2 46 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 131 221 (Polychromatic418967fa.accept_27_18_23_5_1_5277 45 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115
  44 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 221 (accept_3_2 43
  131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 131 221 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 221 (accept_3_2 40 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 131 221 (Polychromatic418967fa.accept_21_18_5_11_1_7013 39 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 38 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 221 (accept_3_2 37 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 221 (accept_3_2 34 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 221 (Polychromatic418967fa.accept_16_1_3_13_1_2785 33 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 221
  (Polychromatic418967fa.accept_20_12_11_1_1_3032 32 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 131 221 (accept_3_2 31 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 131 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 221 (accept_3_2 28 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 221 (Polychromatic418967fa.accept_7_6_5_4_1_297
  27 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 26 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 221 (accept_3_2 25 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 221 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 221 (accept_3_2 22 131 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 221 (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 221
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 221 (accept_3_2 19 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 221 (Polychromatic418967fa.accept_16_1_3_13_1_2785 17 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 221 (accept_3_2 16 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 221 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 14 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 221 (accept_3_2 13 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 221 (Polychromatic418967fa.accept_20_12_11_1_1_3032 12 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 221 (Polychromatic418967fa.accept_22_11_21_1_1_13183 11 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 221 (accept_3_2 10 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 221 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 131 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 221
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 221 (accept_3_2 7 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 221 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 221 (Polychromatic418967fa.accept_19_5_17_12_1_6120 5 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 221 (accept_3_2 4 131 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 221 (Polychromatic418967fa.accept_19_3_17_12_1_6176 3 131
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 221
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 221 (accept_3_2 1 131 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 130 221
  (Eq.refl Bool.true) (allA_of_3_0 92 130 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 129 221 (Eq.refl
  Bool.true) (allA_succ_of_accept 92 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 92 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 221 (accept_3_2 91 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 90 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 89 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 221 (accept_3_2 88 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 87 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 86 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 221 (accept_3_2 85 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 84 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 83 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 221 (accept_3_2 82 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 221 (Polychromatic418967fa.accept_11_4_8_1_1_1047 81 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 221 (accept_3_2 79 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 78 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 221
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 77 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 221 (accept_3_2 76 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 75 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 221 (accept_3_2 73 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 221 (Polychromatic418967fa.accept_10_2_9_1_1_185 72 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 71 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 221 (accept_3_2 70 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 221 (accept_3_2 67 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 221 (Polychromatic418967fa.accept_15_6_9_11_1_858 66 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 65 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 221 (accept_3_2 64 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 63 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 221 (accept_3_2 61 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 221
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 221 (accept_3_2 58 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 221 (accept_3_2 55 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 221 (Polychromatic418967fa.accept_19_16_15_12_1_2266 54 129 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 53 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 221 (accept_3_2 52 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 221 (accept_3_2 49 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 47 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 221 (accept_3_2 46 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 221 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 221 (accept_3_2 43 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 221
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 221 (accept_3_2 40 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 39 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 221 (accept_3_2 37 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 221 (accept_3_2 34 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 221 (accept_3_2 31 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 221 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 129 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 221
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 221 (accept_3_2 28 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 221 (accept_3_2 25 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 221 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 221
  (Polychromatic418967fa.accept_26_23_25_13_1_13182 23 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 129 221 (accept_3_2 22 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 129 221 (Polychromatic418967fa.accept_14_7_3_11_1_2199 21 129 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 221 (accept_3_2 19 129 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 221 (Polychromatic418967fa.accept_10_8_9_1_1_189
  18 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 221
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 221 (accept_3_2 16 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 221 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 221 (accept_3_2 13 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 221 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 221
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 221 (accept_3_2 10 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 221 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 221 (accept_3_2 7 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 221 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 221
  (Polychromatic418967fa.accept_10_5_9_1_1_187 5 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 221 (accept_3_2 4 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 221 (Polychromatic418967fa.accept_12_3_9_5_1_853 3 129 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 221 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 221 (accept_3_2 1 129 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  221))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 128
  221 (Eq.refl Bool.true) (allA_succ_of_accept 93 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 93 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 128 221
  (Polychromatic418967fa.accept_19_16_14_12_1_6261 92 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 128 221 (accept_3_2 91 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 90 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 128 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 89 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 128 221 (accept_3_2 88 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 87
  128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 128 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 86 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 128 221 (accept_3_2 85 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 128 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 84 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 83 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 128 221 (accept_3_2 82 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 80 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 128 221 (accept_3_2 79 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 128 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 78 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 128 221 (Polychromatic418967fa.accept_21_14_2_11_1_8625 77 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 221 (accept_3_2 76 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 74 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 128 221 (accept_3_2 73 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 128 221 (Polychromatic418967fa.accept_11_6_7_1_1_564 72 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 128 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 221 (accept_3_2 70 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 68 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 221 (accept_3_2 67 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 66 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 221 (Polychromatic418967fa.accept_14_9_2_11_1_780 65 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 221 (accept_3_2 64 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 221
  (Polychromatic418967fa.accept_7_6_2_4_1_291 62 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 221 (accept_3_2 61 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 60 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 221 (accept_3_2 58 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 221
  (Polychromatic418967fa.accept_21_14_2_11_1_8625 56 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 221 (accept_3_2 55 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 221 (accept_3_2 52 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 51
  128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 221
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 221 (accept_3_2 49 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 221 (accept_3_2 46 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 44 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 221 (accept_3_2 43 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 42 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 221 (accept_3_2 40 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 221
  (Polychromatic418967fa.accept_12_2_8_5_1_408 38 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 221 (accept_3_2 37 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 221 (Polychromatic418967fa.accept_19_17_14_12_1_2263 36 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 221 (accept_3_2 34 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 221
  (Polychromatic418967fa.accept_19_13_14_12_1_4797 32 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 128 221 (accept_3_2 31 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 128 221 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 221 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 128
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 221 (accept_3_2 28 128
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 128 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 221 (accept_3_2 25 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 128 221 (Polychromatic418967fa.accept_9_6_2_5_1_506 24 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 221 (Polychromatic418967fa.accept_10_3_8_1_1_182
  23 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 221 (accept_3_2 22
  128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 221
  (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 221 (accept_3_2 19 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 128 221 (Polychromatic418967fa.accept_15_3_8_11_1_4386 18 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 221
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 221 (accept_3_2 16 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 14 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 221 (accept_3_2 13 128 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 221 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 221
  (Polychromatic418967fa.accept_20_11_8_1_1_13181 11 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 128 221 (accept_3_2 10 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 221 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 221 (accept_3_2 7 128 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 221 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 221
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 221 (accept_3_2 4 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 221 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 221 (Polychromatic418967fa.accept_12_2_8_5_1_408 2 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 221 (accept_3_2 1 128 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 127
  221 (Eq.refl Bool.true) (allA_of_3_0 95 127 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 126 221
  (Eq.refl Bool.true) (allA_succ_of_accept 95 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 95 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 126 221 (accept_3_2 94 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 126 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 93 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 126 221
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 92 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 126 221 (accept_3_2 91 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 126 221 (Polychromatic418967fa.accept_16_10_14_13_1_1870 90 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 221 (Polychromatic418967fa.accept_23_20_11_14_1_13180 89 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 221 (accept_3_2 88 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 87
  126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 221
  (Polychromatic418967fa.accept_24_14_6_5_1_7999 86 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 126 221 (accept_3_2 85 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 126 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 84 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 83 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 221 (accept_3_2 82 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 221 (Polychromatic418967fa.accept_16_1_14_13_1_3834 81 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 221
  (Polychromatic418967fa.accept_15_5_6_11_1_854 80 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 221 (accept_3_2 79 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 126 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 78 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 126 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 77 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 221 (accept_3_2 76 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 221
  (Polychromatic418967fa.accept_16_10_14_13_1_1870 74 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 126 221 (accept_3_2 73 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 72 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 71 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 221 (accept_3_2 70 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 221
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 69 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 126 221 (Polychromatic418967fa.accept_23_22_11_14_1_9880 68 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 221 (accept_3_2 67 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 221 (Polychromatic418967fa.accept_23_20_11_14_1_13180 66 126 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 65 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 126 221 (accept_3_2 64 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 62 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 221 (accept_3_2 61 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 221 (Polychromatic418967fa.accept_24_12_6_5_1_13097 60 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 59 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 126 221 (accept_3_2 58 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 126 221 (Polychromatic418967fa.accept_10_7_6_1_1_486 57 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 126 221 (Polychromatic418967fa.accept_20_16_6_1_1_7270 56 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 221 (accept_3_2 55 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 54 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 221
  (Polychromatic418967fa.accept_23_7_11_14_1_13177 53 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 126 221 (accept_3_2 52 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 221 (accept_3_2 49 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 126 221
  (Polychromatic418967fa.accept_15_3_6_11_1_855 48 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 47 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 221 (accept_3_2 46 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 126 221 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 221
  (Polychromatic418967fa.accept_27_17_18_5_1_13179 44 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 126 221 (accept_3_2 43 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 221 (Polychromatic418967fa.accept_22_19_16_1_1_13178 41
  126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 221 (accept_3_2 40
  126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 221 (Polychromatic418967fa.accept_24_14_6_5_1_7999 38 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 221 (accept_3_2 37 126 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 221 (Polychromatic418967fa.accept_20_16_6_1_1_7270 36 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 35 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 126 221 (accept_3_2 34 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 126 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 221 (accept_3_2 31 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 221 (Polychromatic418967fa.accept_23_7_11_14_1_13177 30
  126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 221
  (Polychromatic418967fa.accept_22_7_16_1_1_8414 29 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 126 221 (accept_3_2 28 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 126 221 (Polychromatic418967fa.accept_16_10_14_13_1_1870 26 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 221 (accept_3_2 25 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 23 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 221 (accept_3_2 22 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 126 221 (Polychromatic418967fa.accept_22_21_16_1_1_6739 21 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 126 221 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 221 (accept_3_2 19 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 221 (Polychromatic418967fa.accept_15_3_6_11_1_855 18 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 221
  (Polychromatic418967fa.accept_10_7_6_1_1_486 17 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 221 (accept_3_2 16 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 126 221 (Polychromatic418967fa.accept_20_14_6_1_1_3023 14 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 126 221 (accept_3_2 13 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 126
  221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 221
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 126 221 (accept_3_2 10 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  126 221 (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 126 221 (Polychromatic418967fa.accept_24_8_6_5_1_1399 8 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 221 (accept_3_2 7 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 126 221 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 126 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 221
  (Polychromatic418967fa.accept_10_5_6_1_1_836 5 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 221 (accept_3_2 4 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  126 221 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 126 221 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 221 (accept_3_2 1 126 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 126
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 125
  221 (Eq.refl Bool.true) (allA_succ_of_accept 96 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 96 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 125 221
  (Polychromatic418967fa.accept_20_15_5_1_1_5899 95 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 125 221 (accept_3_2 94 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 93 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 125 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 92 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 125 221 (accept_3_2 91 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 125 221 (Polychromatic418967fa.accept_20_10_5_1_1_4406 90 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 125 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 89 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 125 221 (accept_3_2 88 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 87 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 86 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 125 221 (accept_3_2 85 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 125 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 84 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 125 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 83 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 125 221 (accept_3_2 82 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 125 221 (Polychromatic418967fa.accept_15_6_5_11_1_2378 81 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 80 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 125 221 (accept_3_2 79 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 78 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 125 221
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 77 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 125 221 (accept_3_2 76 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 125 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 74 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 125 221 (accept_3_2 73 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 72 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 221
  (Polychromatic418967fa.accept_21_8_20_11_1_7025 71 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 125 221 (accept_3_2 70 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 69 125 221 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 125 221 (accept_3_2 67 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 66
  125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 125 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 65 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 125 221 (accept_3_2 64 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 125 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 125 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 62 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 221 (accept_3_2 61 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 125 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 221 (accept_3_2 58 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 57 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 56 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 221 (accept_3_2 55 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 221
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 53 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 221 (accept_3_2 52 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 221 (Polychromatic418967fa.accept_20_10_5_1_1_4406 50 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 221 (accept_3_2 49 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 221 (accept_3_2 46 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 44 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 221 (accept_3_2 43 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 221
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 221 (accept_3_2 40 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 39 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 221 (accept_3_2 37 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 221 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 221
  (Polychromatic418967fa.accept_20_15_5_1_1_5899 35 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 221 (accept_3_2 34 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 221 (Polychromatic418967fa.accept_15_2_5_11_1_1563 32 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 221 (accept_3_2 31 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 221 (accept_3_2 28 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 221 (Polychromatic418967fa.accept_19_8_11_12_1_6165 27 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 221 (accept_3_2 25 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 221
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 221 (accept_3_2 22 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 221 (Polychromatic418967fa.accept_9_3_8_5_1_65 21 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 221 (Polychromatic418967fa.accept_9_2_8_5_1_228 20 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 221 (accept_3_2 19 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 221 (Polychromatic418967fa.accept_19_18_11_12_1_6163 18 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 221
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 221 (accept_3_2 16 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 15 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 221 (Polychromatic418967fa.accept_10_4_5_1_1_497 14 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 221 (accept_3_2 13 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 221 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 221
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 221
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 221 (accept_3_2 10 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 221 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 221 (accept_3_2 7 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 221 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 125 221 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 221
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 221 (accept_3_2 4 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 221 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 125 221 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 221 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 221 (accept_3_2 1 125 221 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125
  221)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_221_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


