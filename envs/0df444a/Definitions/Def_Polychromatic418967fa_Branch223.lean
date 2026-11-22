-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch223
-- name    : Polychromatic418967fa_Branch223
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:25:22.739+00:00
-- url     : https://prove2.me/theorems/4c0b2bda-d877-4964-af94-aa75413c6412
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch223_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_223 : allB 223 223 :=
  allB_succ' 2 222 223 (Eq.refl Bool.true) (allA_succ_of_accept 1 222 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  222 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 222 223)) (allB_succ' 3 221 223
  (Eq.refl Bool.true) (allA_of_3_1 3 221 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 220 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 220 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 220 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 220 223 (accept_3_3 2 220 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 220 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 220 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 220 223)))) (allB_succ' 5 219 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 219 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 219 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 219 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 219 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 219 223 (accept_3_3 2 219 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 219 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  219 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 223))))) (allB_succ' 6 218 223
  (Eq.refl Bool.true) (allA_of_3_1 6 218 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 217 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 217 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 217 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 217 223 (accept_3_3 5 217 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 217 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 217 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 217 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 217 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 217 223 (accept_3_3 2 217 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  217 223 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 217 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 217 223))))))) (allB_succ' 8 216 223 (Eq.refl Bool.true) (allA_succ_of_accept 7 216 223
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 216 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 216 223 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 216 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 216 223 (accept_3_3 5 216 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 216 223 (Polychromatic418967fa.accept_11_4_7_3_1_289 4 216 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 216 223 (Polychromatic418967fa.accept_19_3_7_14_1_3669
  3 216 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 216 223 (accept_3_3 2
  216 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 216 223
  (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 216 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 216 223)))))))) (allB_succ' 9 215 223 (Eq.refl Bool.true) (allA_of_3_1 9 215 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 214 223 (Eq.refl Bool.true) (allA_succ_of_accept 9 214 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 214 223 (accept_3_3 8 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  214 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 214 223 (Polychromatic418967fa.accept_15_6_4_13_1_403 6 214 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 214 223 (accept_3_3 5 214 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 214 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 214 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 214 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 214 223 (accept_3_3 2 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  214 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 214 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 214 223)))))))))) (allB_succ' 11 213 223 (Eq.refl Bool.true) (allA_succ_of_accept 10 213 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 213 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 213 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 213 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 213 223 (accept_3_3 8 213 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 213 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 213 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 213 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  213 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 223 (accept_3_3 5 213
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 213 223 (Polychromatic418967fa.accept_6_4_3_1_1_57
  4 213 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 213 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 213 223 (accept_3_3 2 213 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  213 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 213 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 213 223))))))))))) (allB_succ' 12 212 223 (Eq.refl Bool.true) (allA_of_3_1 12 212 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 211 223 (Eq.refl Bool.true) (allA_succ_of_accept 12 211 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 211 223 (accept_3_3 11 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 211 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 211 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 211 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 223 (accept_3_3 8 211 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 211 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 223 (accept_3_3 5 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 211 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 211 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 223 (accept_3_3 2 211 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 211 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 223))))))))))))) (allB_succ' 14 210 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 210 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 210 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 210 223
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 210 223 (accept_3_3 11 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 210 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 210 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 210 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 210 223 (accept_3_3 8 210 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 210 223 (Polychromatic418967fa.accept_20_7_10_3_1_949 7 210 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 210 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 223 (accept_3_3 5 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  210 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 210 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 223 (Polychromatic418967fa.accept_16_3_2_15_1_7367 3 210 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 223 (accept_3_3 2 210 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 210 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 223)))))))))))))) (allB_succ' 15 209 223
  (Eq.refl Bool.true) (allA_of_3_1 15 209 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 208 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 208 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 208 223 (accept_3_3 14 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 208 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 208 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 208 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 208 223 (accept_3_3 11 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 208 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 208 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 223 (accept_3_3 8 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 208 223 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 208 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 223 (accept_3_3 5 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 208 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 223 (accept_3_3 2 208 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 208 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 223)))))))))))))))) (allB_succ' 17 207 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 207 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 207 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 207 223 (Polychromatic418967fa.accept_10_5_7_3_1_561
  15 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 207 223 (accept_3_3 14
  207 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 207 223
  (Polychromatic418967fa.accept_24_13_15_7_1_13263 13 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 207 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 207 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 223 (accept_3_3 11 207 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 207 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 207 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 223 (accept_3_3 8 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 223 (Polychromatic418967fa.accept_21_7_18_13_1_5585 7 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 207 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 223 (accept_3_3 5 207 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 223 (accept_3_3 2 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 223 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 207 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 223))))))))))))))))) (allB_succ' 18 206 223 (Eq.refl Bool.true) (allA_of_3_1 18 206 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 205 223 (Eq.refl Bool.true) (allA_succ_of_accept 18 205 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 205 223 (accept_3_3 17 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 205 223 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 205 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 205 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 205 223 (accept_3_3 14 205 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 223 (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 205 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 205 223
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 223 (accept_3_3 11 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 223 (Polychromatic418967fa.accept_21_9_16_13_1_1541 9 205 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 223 (accept_3_3 8 205 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 205 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 223 (accept_3_3 5 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 205 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 205 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 223 (accept_3_3 2 205 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 205 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 223))))))))))))))))))) (allB_succ' 20 204 223
  (Eq.refl Bool.true) (allA_succ_of_accept 19 204 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 204 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 204 223
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 204 223 (accept_3_3 17 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 204 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 204 223 (Polychromatic418967fa.accept_30_15_24_13_1_13320 15 204 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 204 223 (accept_3_3 14 204 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 204 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 204 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 204 223 (accept_3_3 11 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 204 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 204 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 223 (accept_3_3 8 204 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 204 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 223
  (Polychromatic418967fa.accept_13_6_9_2_1_838 6 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 223 (accept_3_3 5 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 204 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 204 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 223 (accept_3_3 2 204 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 223)))))))))))))))))))) (allB_succ' 21 203 223
  (Eq.refl Bool.true) (allA_of_3_1 21 203 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 202 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 202 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 202 223 (accept_3_3 20 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 202 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 202 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 202 223
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 202 223 (accept_3_3 17 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 202 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 202 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 223 (accept_3_3 14 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 202 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 202 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 223 (accept_3_3 11 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 202 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 223 (accept_3_3 8 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 202 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 223 (accept_3_3 5 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 202 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 223 (accept_3_3 2 202 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 223)))))))))))))))))))))) (allB_succ' 23 201 223
  (Eq.refl Bool.true) (allA_succ_of_accept 22 201 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 201 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 201 223
  (Polychromatic418967fa.accept_13_8_6_2_1_865 21 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 201 223 (accept_3_3 20 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 201 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 201 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 201 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 223 (accept_3_3 17 201 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 201 223 (accept_3_3 14 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 201 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 201 223 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 201 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 223 (accept_3_3 11 201 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 201 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 223
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 223 (accept_3_3 8 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 223 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 223 (accept_3_3 5 201 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 223 (accept_3_3 2 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 201 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 223))))))))))))))))))))))) (allB_succ' 24 200 223 (Eq.refl Bool.true) (allA_of_3_1 24 200
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 199 223 (Eq.refl Bool.true) (allA_succ_of_accept 24 199
  223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 199 223 (accept_3_3 23 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 199 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 199 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 199 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 199 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 199 223 (accept_3_3 20 199 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 199 223 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  19 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 199 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 223 (accept_3_3 17 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 199 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 223 (accept_3_3 14 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 199 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 223 (accept_3_3 11 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 223 (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 223 (accept_3_3 8 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 223 (Polychromatic418967fa.accept_17_7_12_2_1_7105 7 199 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 223 (accept_3_3 5 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 199 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 223 (accept_3_3 2 199 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 223 (Polychromatic418967fa.accept_19_1_9_14_1_526 1 199 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 223))))))))))))))))))))))))) (allB_succ' 26 198 223
  (Eq.refl Bool.true) (allA_succ_of_accept 25 198 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 198 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 198 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 198 223 (accept_3_3 23 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 198 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 198 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 198 223 (accept_3_3 20 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 198 223 (Polychromatic418967fa.accept_27_19_9_7_1_7350 19 198 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 223 (accept_3_3 17 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 223 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 223 (accept_3_3 14 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 198 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 223
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 223 (accept_3_3 11 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 198 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 223 (accept_3_3 8 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 223 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 198 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 223
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 223 (accept_3_3 5 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 198 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 223 (accept_3_3 2 198 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 223)))))))))))))))))))))))))) (allB_succ' 27 197 223
  (Eq.refl Bool.true) (allA_of_3_1 27 197 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 196 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 196 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 196 223 (accept_3_3 26 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 196 223 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 196 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 196 223
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 196 223 (accept_3_3 23 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 196 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 196 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 196 223 (accept_3_3 20 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 196 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 196 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 223
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 196 223 (accept_3_3 17 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 196 223 (Polychromatic418967fa.accept_13_3_1_2_1_2960 16 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 196 223 (accept_3_3 14 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 196 223 (Polychromatic418967fa.accept_20_13_16_3_1_4479 13 196 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 196 223
  (Polychromatic418967fa.accept_13_12_1_2_1_845 12 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 196 223 (accept_3_3 11 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 196 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 196 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 223 (accept_3_3 8 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 196 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 196 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 223
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 196 223 (accept_3_3 5 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  196 223 (Polychromatic418967fa.accept_17_4_9_2_1_9721 4 196 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 196 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 223 (accept_3_3 2 196 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 223 (Polychromatic418967fa.accept_18_1_16_7_1_2897 1 196 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 223)))))))))))))))))))))))))))) (allB_succ' 29 195
  223 (Eq.refl Bool.true) (allA_succ_of_accept 28 195 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 195 223
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 195 223 (accept_3_3 26 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 195 223 (Polychromatic418967fa.accept_19_6_5_14_1_3582 25 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 195 223 (Polychromatic418967fa.accept_21_3_6_13_1_8756 24 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 223 (accept_3_3 23 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 195 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 223 (accept_3_3 20 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 195 223 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 223 (accept_3_3 17 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 223
  (Polychromatic418967fa.accept_21_15_6_13_1_8776 15 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 223 (accept_3_3 14 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 195 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 195 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 223 (accept_3_3 11 195 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10
  195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 223 (accept_3_3 8 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 223 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 195 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 223 (accept_3_3 5 195 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 223 (accept_3_3 2 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 195 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 223))))))))))))))))))))))))))))) (allB_succ' 30 194 223 (Eq.refl Bool.true) (allA_of_3_1 30
  194 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 193 223 (Eq.refl Bool.true) (allA_succ_of_accept 30
  193 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 193 223 (accept_3_3 29 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 193 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 193 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 193 223 (Polychromatic418967fa.accept_16_11_1_15_1_1123 27 193
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 223 (accept_3_3 26 193
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 223
  (Polychromatic418967fa.accept_23_2_9_16_1_13319 25 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 193 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 223 (accept_3_3 23 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 193 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 193 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 193 223 (accept_3_3 20 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 193 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 223 (accept_3_3 17 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 193 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 223 (accept_3_3 14 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 223 (Polychromatic418967fa.accept_17_13_6_2_1_5850 13 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 223 (accept_3_3 11 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 223 (accept_3_3 8 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 223 (Polychromatic418967fa.accept_19_7_3_14_1_5023 7 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 223 (accept_3_3 5 193 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 223 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 193 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 223 (accept_3_3 2 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 223))))))))))))))))))))))))))))))) (allB_succ' 32 192 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 31 192 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 192 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 192 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 192 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 192 223 (accept_3_3 29 192 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 192 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 28
  192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 192 223
  (Polychromatic418967fa.accept_19_8_2_14_1_3640 27 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 192 223 (accept_3_3 26 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 192 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 192 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 223 (accept_3_3 23 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 192 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 223
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 223 (accept_3_3 20 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 192 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 223 (accept_3_3 17 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 192 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 192 223 (accept_3_3 14 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 192 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 192 223 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 192 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 223 (accept_3_3 11 192 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 192 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 223 (accept_3_3 8 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  192 223 (Polychromatic418967fa.accept_19_7_2_14_1_3569 7 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 223 (accept_3_3 5 192 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 192 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 223
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 192 223 (accept_3_3 2 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  192 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 192 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192 223)))))))))))))))))))))))))))))))) (allB_succ' 33 191 223 (Eq.refl Bool.true) (allA_of_3_1
  33 191 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 190 223 (Eq.refl Bool.true) (allA_succ_of_accept 33
  190 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 190 223 (accept_3_3 32 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 190 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 190 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 190 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 190 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 190 223 (accept_3_3 29 190 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 190 223 (Polychromatic418967fa.accept_12_4_10_7_1_149
  28 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 190 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 190 223 (accept_3_3 26 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 190 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 190 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 190 223 (accept_3_3 23 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 190 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 190 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 190 223 (accept_3_3 20 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 190 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 190 223 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 190 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 223 (accept_3_3 17 190 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 190 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 190 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 190 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 190 223 (accept_3_3 14 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 190 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 190 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 190 223 (accept_3_3 11 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 190 223 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 190 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 190 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 190 223 (accept_3_3 8 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  190 223 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 190 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 223 (accept_3_3 5 190 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 190 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 190 223 (accept_3_3 2 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  190 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 223)))))))))))))))))))))))))))))))))) (allB_succ' 35 189 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 34 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 189 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 189 223 (Polychromatic418967fa.accept_15_3_9_13_1_1681 33 189
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 189 223 (accept_3_3 32 189
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 189 223
  (Polychromatic418967fa.accept_13_5_7_2_1_852 31 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 189 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 223 (accept_3_3 29 189 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 189 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 189 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 223 (Polychromatic418967fa.accept_12_3_9_7_1_472
  27 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 223 (accept_3_3 26
  189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 223
  (Polychromatic418967fa.accept_37_25_4_1_1_13318 25 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 189 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 223 (accept_3_3 23 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 189 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 223
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 189 223 (accept_3_3 20 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 189 223 (Polychromatic418967fa.accept_15_4_9_13_1_2582 19 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 223 (accept_3_3 17 189 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 223 (accept_3_3 14 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 223 (Polychromatic418967fa.accept_19_13_18_14_1_3522 13 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 223 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 223 (accept_3_3 11 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 223
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 223 (accept_3_3 8 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 223 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 223 (accept_3_3 5 189 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 223 (accept_3_3 2 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 223 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 189 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 223))))))))))))))))))))))))))))))))))) (allB_succ' 36 188 223 (Eq.refl Bool.true)
  (allA_of_3_1 36 188 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 187 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 187 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 187 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 187 223 (accept_3_3 35 187 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 187 223 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 187 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 187 223 (Polychromatic418967fa.accept_13_7_5_2_1_401
  33 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 187 223 (accept_3_3 32
  187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 223
  (Polychromatic418967fa.accept_19_12_16_14_1_3661 31 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 187 223 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 187 223 (accept_3_3 29 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 187 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 187 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 223
  (Polychromatic418967fa.accept_21_6_19_13_1_7196 27 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 187 223 (accept_3_3 26 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 187 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 187 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 223 (Polychromatic418967fa.accept_10_4_7_3_1_54 24 187 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 223 (accept_3_3 23 187 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 22
  187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 223
  (Polychromatic418967fa.accept_15_6_7_13_1_1666 21 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 223 (accept_3_3 20 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 223 (Polychromatic418967fa.accept_16_3_11_15_1_1963 19 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 187 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 223 (accept_3_3 17 187 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 223 (accept_3_3 14 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 223 (Polychromatic418967fa.accept_19_13_16_14_1_3517 13 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 223 (accept_3_3 11 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 223 (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 187
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 223
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 223 (accept_3_3 8 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 223 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 6 187 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 223 (accept_3_3 5 187 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 187 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 223
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 223 (accept_3_3 2 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 187 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 223))))))))))))))))))))))))))))))))))))) (allB_succ' 38 186 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 186 223 (Polychromatic418967fa.accept_19_17_15_14_1_3623 36
  186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 186 223 (accept_3_3 35
  186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 186 223
  (Polychromatic418967fa.accept_15_4_6_13_1_956 34 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 186 223 (accept_3_3 32 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 186 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 186 223 (Polychromatic418967fa.accept_7_2_4_6_1_166
  30 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 223 (accept_3_3 29
  186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 223
  (Polychromatic418967fa.accept_9_1_6_7_1_285 28 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 186 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 223 (accept_3_3 26 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 186 223 (Polychromatic418967fa.accept_7_3_4_6_1_329
  24 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 223 (accept_3_3 23
  186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 223
  (Polychromatic418967fa.accept_9_4_6_7_1_286 22 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 223 (accept_3_3 20 186 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 186 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394
  18 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 223 (accept_3_3 17
  186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 186 223 (Polychromatic418967fa.accept_21_15_18_13_1_8747 15 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 223 (accept_3_3 14 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 223
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 223 (accept_3_3 11 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 223 (accept_3_3 8 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 186 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 223
  (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 223 (accept_3_3 5 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 186 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 223 (accept_3_3 2 186 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 223))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 185 223 (Eq.refl Bool.true) (allA_of_3_1 39 185 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 184 223 (Eq.refl Bool.true) (allA_succ_of_accept 39 184 223 (Polychromatic418967fa.accept_6_3_4_1_1_8
  39 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 184 223 (accept_3_3 38
  184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 184 223
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 184 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 184 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 184 223 (accept_3_3 35 184 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 184 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 184 223 (accept_3_3 32 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 184 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 184 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 223 (accept_3_3 29 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 184 223 (accept_3_3 26 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 184 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 184 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 223 (accept_3_3 23 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 184 223 (accept_3_3 20 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 184 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 184 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 223 (accept_3_3 17 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 223 (Polychromatic418967fa.accept_11_5_8_3_1_66 16 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 184 223 (accept_3_3 14 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 184 223 (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 184 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 184 223 (accept_3_3 11 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 223 (accept_3_3 8 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 223 (accept_3_3 5 184 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 184 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 223 (accept_3_3 2 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 184 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 223)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 183 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 183 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 223 (Polychromatic418967fa.accept_15_9_3_13_1_1686 39 183
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 223 (accept_3_3 38 183
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 183 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 183 223 (Polychromatic418967fa.accept_19_17_12_14_1_3655 36 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 223 (accept_3_3 35 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 223 (accept_3_3 32 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 223 (accept_3_3 29 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 223
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 223 (accept_3_3 26 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 223 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 183 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 183 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 223 (accept_3_3 23 183 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 223
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 223 (accept_3_3 20 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 223 (Polychromatic418967fa.accept_17_1_13_2_1_7086 18 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 223 (accept_3_3 17 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 223 (accept_3_3 14 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 223 (accept_3_3 11 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 223 (accept_3_3 8 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 223 (accept_3_3 5 183 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 223
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 223 (accept_3_3 2 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 183 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 223))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 182 223 (Eq.refl Bool.true)
  (allA_of_3_1 42 182 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 181 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 42 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 181 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 181 223 (accept_3_3 41 181 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 181 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 181 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 39
  181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 223 (accept_3_3 38
  181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 223
  (Polychromatic418967fa.accept_17_3_11_2_1_8435 37 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 181 223 (Polychromatic418967fa.accept_13_10_12_2_1_1460 36 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 223 (accept_3_3 35 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 223 (accept_3_3 32 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 223 (accept_3_3 29 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 223 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 223
  (Polychromatic418967fa.accept_13_1_12_2_1_384 27 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 223 (accept_3_3 26 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 223 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 223 (accept_3_3 23 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 223 (accept_3_3 20 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 223 (Polychromatic418967fa.accept_11_8_5_3_1_694 19 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 223 (accept_3_3 17 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 223 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 223 (accept_3_3 14 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 223 (accept_3_3 11 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 223
  (Polychromatic418967fa.accept_17_9_11_2_1_5894 9 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 223 (accept_3_3 8 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 223 (Polychromatic418967fa.accept_19_7_10_14_1_3599 7 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 223 (accept_3_3 5 181 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 181 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 223 (accept_3_3 2 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 223 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 181 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 223))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 180 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 180 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 180 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 180 223 (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 180
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 180 223 (accept_3_3 41 180
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 180 223
  (Polychromatic418967fa.accept_11_7_4_3_1_302 40 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 180 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 180 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 180 223 (accept_3_3 38 180 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 180 223 (Polychromatic418967fa.accept_16_5_4_15_1_1102 37 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 180 223 (accept_3_3 35 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 180 223 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 180 223 (Polychromatic418967fa.accept_24_9_12_7_1_13317 33 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 223 (accept_3_3 32 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 223 (Polychromatic418967fa.accept_19_12_9_14_1_6365 31 180
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 223
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 180 223 (accept_3_3 29 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 180 223 (Polychromatic418967fa.accept_16_12_4_15_1_5091 28 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 180 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 223 (accept_3_3 26 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 223
  (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 180 223 (accept_3_3 23 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 180 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 180 223 (Polychromatic418967fa.accept_16_5_4_15_1_1102 21 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 223 (accept_3_3 20 180 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 180 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 223 (accept_3_3 17 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 180 223 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 223 (accept_3_3 14 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 223 (Polychromatic418967fa.accept_22_13_4_3_1_13316 13 180 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 223
  (Polychromatic418967fa.accept_16_12_4_15_1_5091 12 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 180 223 (accept_3_3 11 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 223 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 223 (Polychromatic418967fa.accept_13_9_11_2_1_1491
  9 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 223 (accept_3_3 8
  180 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 223
  (Polychromatic418967fa.accept_11_7_4_3_1_302 7 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 180 223 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 180 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 180 223 (accept_3_3 5 180 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 180 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 180 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 223 (accept_3_3 2 180
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 223 (Polychromatic418967fa.accept_7_1_5_6_1_59
  1 180 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  223)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 179 223 (Eq.refl Bool.true) (allA_of_3_1 45 179 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 178 223 (Eq.refl Bool.true) (allA_succ_of_accept 45 178 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 178 223 (accept_3_3 44 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 178 223 (Polychromatic418967fa.accept_21_1_10_13_1_5623 43 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 178 223 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 178 223 (accept_3_3 41 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 178 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 40 178
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 178 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 178 223 (accept_3_3 38 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 178 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 178 223 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 223 (accept_3_3 35 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 178 223 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 178
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 223 (accept_3_3 32 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 223 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 223 (accept_3_3 29 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 223 (accept_3_3 26 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 223 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 223 (accept_3_3 23 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 223 (Polychromatic418967fa.accept_18_4_16_7_1_1873 22 178
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 223 (accept_3_3 20 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 223 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 223 (accept_3_3 17 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 223 (accept_3_3 14 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 223 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 223 (accept_3_3 11 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 223 (Polychromatic418967fa.accept_17_10_8_2_1_8411 10 178
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 223 (accept_3_3 8 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 223 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 223 (Polychromatic418967fa.accept_10_6_8_3_1_930 6 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 223 (accept_3_3 5 178 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 178 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 223 (accept_3_3 2 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 223)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 177 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 177 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 177 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 177 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 223 (accept_3_3 44 177 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 177 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 43
  177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 223 (accept_3_3 41 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 223 (accept_3_3 38 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 223
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 223 (accept_3_3 35 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 223 (Polychromatic418967fa.accept_13_7_8_2_1_1483 33 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 223 (accept_3_3 32 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 177 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 223 (accept_3_3 29 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 223 (Polychromatic418967fa.accept_12_3_9_7_1_472 27 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 223 (accept_3_3 26 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 177 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 223 (accept_3_3 23 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 223 (accept_3_3 20 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 223 (accept_3_3 17 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 223 (accept_3_3 14 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 223 (accept_3_3 11 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 223 (Polychromatic418967fa.accept_17_9_7_2_1_2347 9 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 223 (accept_3_3 8 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 223 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 223 (accept_3_3 5 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 223 (accept_3_3 2 177 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 177 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 223)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 176 223 (Eq.refl Bool.true) (allA_of_3_1 48 176 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 175 223 (Eq.refl Bool.true) (allA_succ_of_accept 48 175 223 (Polychromatic418967fa.accept_9_3_4_7_1_89
  48 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 175 223 (accept_3_3 47
  175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 175 223
  (Polychromatic418967fa.accept_9_1_4_7_1_7 46 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 175 223 (Polychromatic418967fa.accept_19_7_4_14_1_5003 45 175 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 175 223 (accept_3_3 44 175 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 175 223 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 175 223 (accept_3_3 41 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 175 223 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 175 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 223 (accept_3_3 38 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 223
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 175 223 (accept_3_3 35 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 175 223 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 175 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 223 (accept_3_3 32 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 175 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 31 175 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 223 (accept_3_3 29 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 175 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 175 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 223 (accept_3_3 26 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 223 (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 175
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 175 223 (accept_3_3 23 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 175 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 175 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 223 (accept_3_3 20 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 223
  (Polychromatic418967fa.accept_10_8_5_3_1_543 18 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 223 (accept_3_3 17 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 223 (accept_3_3 14 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 223 (Polychromatic418967fa.accept_19_13_4_14_1_11912 13 175 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 223 (accept_3_3 11 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 223 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 223 (accept_3_3 8 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 223 (accept_3_3 5 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 223 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 175 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 223 (accept_3_3 2 175 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 175 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 223)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 174 223 (Eq.refl Bool.true) (allA_succ_of_accept 49 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9
  49 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 174 223
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 174 223 (accept_3_3 47 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 174 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 174 223 (accept_3_3 44 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 174 223 (Polychromatic418967fa.accept_13_4_5_2_1_1436 43 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 174 223 (accept_3_3 41 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 174 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 174 223 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 223 (accept_3_3 38 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 174 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 223
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 36 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 174 223 (accept_3_3 35 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 174 223 (Polychromatic418967fa.accept_15_4_9_13_1_2582 34 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 223 (accept_3_3 32 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 223
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 174 223 (accept_3_3 29 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 174 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 174 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 223 (accept_3_3 26 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 174 223 (accept_3_3 23 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 174 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 223 (accept_3_3 20 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 223
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 223 (accept_3_3 17 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 223 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 223 (accept_3_3 14 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 223
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 174 223 (accept_3_3 11 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 174 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 223 (accept_3_3 8 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 223 (accept_3_3 5 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 174 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 223 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 223 (accept_3_3 2 174 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  223)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 173 223 (Eq.refl Bool.true) (allA_of_3_1 51 173
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 172 223 (Eq.refl Bool.true) (allA_succ_of_accept 51 172
  223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 172 223 (accept_3_3 50 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 172 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 172 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 172 223 (accept_3_3 47 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 172 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 172 223 (accept_3_3 44 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 172 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 172 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 223 (accept_3_3 41 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 223 (accept_3_3 38 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 223 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 223 (accept_3_3 35 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 172
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 223 (accept_3_3 32 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 223 (accept_3_3 29 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 223 (Polychromatic418967fa.accept_19_9_1_14_1_1372 28 172 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 223 (accept_3_3 26 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 223 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 223 (accept_3_3 23 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 223 (accept_3_3 20 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 223 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 223 (accept_3_3 17 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 172 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 223 (accept_3_3 14 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 223 (accept_3_3 11 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 223 (accept_3_3 8 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 223 (Polychromatic418967fa.accept_21_7_4_13_1_4125 7 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 223 (accept_3_3 5 172 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 172 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 223 (accept_3_3 2 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 223 (Polychromatic418967fa.accept_10_1_2_3_1_1910 1 172 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 223)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 171 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 52 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 171 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 51
  171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 171 223 (accept_3_3 50
  171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 223
  (Polychromatic418967fa.accept_15_4_6_13_1_956 49 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 171 223 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 171 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 223 (accept_3_3 47 171 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 223 (Polychromatic418967fa.accept_12_9_3_7_1_924
  45 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 223 (accept_3_3 44
  171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 223
  (Polychromatic418967fa.accept_24_19_3_7_1_13315 43 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 171 223 (Polychromatic418967fa.accept_10_2_1_3_1_233 42 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 223 (accept_3_3 41 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 171 223 (accept_3_3 38 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 171 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 171 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 223 (accept_3_3 35 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 223 (accept_3_3 32 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 223 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 223 (accept_3_3 29 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 223
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 27 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 223 (accept_3_3 26 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 223 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 223 (accept_3_3 23 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 171 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 223 (accept_3_3 20 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 223 (accept_3_3 17 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 223
  (Polychromatic418967fa.accept_27_15_9_7_1_5390 15 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 223 (accept_3_3 14 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 223 (Polychromatic418967fa.accept_17_13_1_2_1_9714 13 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 223 (accept_3_3 11 171 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 223 (accept_3_3 8 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 223 (Polychromatic418967fa.accept_15_7_6_13_1_936 7 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 223 (Polychromatic418967fa.accept_17_6_1_2_1_10823 6 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 223 (accept_3_3 5 171 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 223
  (Polychromatic418967fa.accept_16_3_11_15_1_1963 3 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 223 (accept_3_3 2 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 223 (Polychromatic418967fa.accept_16_1_11_15_1_498 1 171 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 223))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 170 223 (Eq.refl
  Bool.true) (allA_of_3_1 54 170 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 169 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 169 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 169 223 (accept_3_3 53 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 169 223 (Polychromatic418967fa.accept_17_1_16_2_1_1404 52 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 169 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 169 223 (accept_3_3 50 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 169 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 49 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 169 223 (Polychromatic418967fa.accept_17_14_16_2_1_4553 48 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 223 (accept_3_3 47 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 169 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 169 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 223
  (Polychromatic418967fa.accept_22_1_15_3_1_13314 45 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 169 223 (accept_3_3 44 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 169 223 (Polychromatic418967fa.accept_19_5_17_14_1_3627 43 169 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42
  169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 223 (accept_3_3 41
  169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 40 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 169 223 (Polychromatic418967fa.accept_15_9_4_13_1_4482 39 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 223 (accept_3_3 38 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 169 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 169 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 223 (Polychromatic418967fa.accept_10_6_9_3_1_935
  36 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 223 (accept_3_3 35
  169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 169 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 223 (accept_3_3 32 169 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 169 223 (Polychromatic418967fa.accept_17_14_16_2_1_4553 31 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 223 (accept_3_3 29 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 223 (Polychromatic418967fa.accept_19_9_17_14_1_6357 28 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 223 (Polychromatic418967fa.accept_22_5_15_3_1_5261 27 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 223 (accept_3_3 26 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 223 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 169
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 223
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 223 (accept_3_3 23 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 21 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 223 (accept_3_3 20 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 223 (accept_3_3 17 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 223 (Polychromatic418967fa.accept_19_15_17_14_1_1370 15 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 223 (accept_3_3 14 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 223 (Polychromatic418967fa.accept_23_13_8_16_1_13313 13
  169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 223 (accept_3_3 11 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 223 (accept_3_3 8 169 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 223 (accept_3_3 5 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 4 169 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 223 (Polychromatic418967fa.accept_19_3_17_14_1_2354 3 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 223 (accept_3_3 2 169 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 223 (Polychromatic418967fa.accept_17_1_16_2_1_1404 1 169
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 168 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 168 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 168 223 (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 168
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 168 223 (accept_3_3 53 168
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 168 223
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 168 223 (Polychromatic418967fa.accept_10_1_8_3_1_947 51 168 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 168 223 (accept_3_3 50 168 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 168 223 (Polychromatic418967fa.accept_9_3_6_7_1_562
  48 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 168 223 (accept_3_3 47
  168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 223
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 168 223 (Polychromatic418967fa.accept_10_5_8_3_1_229 45 168 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 168 223 (accept_3_3 44 168 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 168 223 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 223
  (Polychromatic418967fa.accept_13_3_12_2_1_385 42 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 168 223 (accept_3_3 41 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 168 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 223 (accept_3_3 38 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 223
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 168 223 (accept_3_3 35 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 168 223 (Polychromatic418967fa.accept_20_14_8_3_1_6011 34 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 168 223 (Polychromatic418967fa.accept_16_1_8_15_1_1945 33 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 223 (accept_3_3 32 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 168 223 (accept_3_3 29 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 168 223 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 223 (accept_3_3 26 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 223 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 168
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 223
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 24 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 168 223 (accept_3_3 23 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 168 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 223 (accept_3_3 20 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 223
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 168 223 (accept_3_3 17 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 168 223 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 168 223 (Polychromatic418967fa.accept_10_5_8_3_1_229 15 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 223 (accept_3_3 14 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 168 223 (accept_3_3 11 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 168 223 (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 223 (accept_3_3 8 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 223 (Polychromatic418967fa.accept_16_7_8_15_1_6327 7 168
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 223
  (Polychromatic418967fa.accept_10_6_8_3_1_930 6 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 168 223 (accept_3_3 5 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  168 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 168 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 168 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 223 (accept_3_3 2 168 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 167 223 (Eq.refl Bool.true) (allA_of_3_1 57
  167 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 166 223 (Eq.refl Bool.true) (allA_succ_of_accept 57
  166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 166 223 (accept_3_3 56 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 166 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 166 223 (Polychromatic418967fa.accept_25_4_16_23_1_13312 54
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 166 223 (accept_3_3 53
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 166 223
  (Polychromatic418967fa.accept_12_4_10_7_1_149 52 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 166 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 223 (accept_3_3 50 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 48
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 166 223 (accept_3_3 47
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 166 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 223 (accept_3_3 44 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 166 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 223 (Polychromatic418967fa.accept_9_6_4_7_1_300
  42 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 166 223 (accept_3_3 41
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 166 223
  (Polychromatic418967fa.accept_12_4_10_7_1_149 40 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 166 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 223 (accept_3_3 38 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 36
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 223 (accept_3_3 35
  166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 223
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 34 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 223 (accept_3_3 32 166 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 166 223 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 223 (accept_3_3 29 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 223 (accept_3_3 26 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 223 (accept_3_3 23 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 223 (accept_3_3 20 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 223 (accept_3_3 17 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 223 (accept_3_3 14 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 223 (accept_3_3 11 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 223 (accept_3_3 8 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 223 (accept_3_3 5 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 166 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 223 (accept_3_3 2 166 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 165 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 165 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 165 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 165 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 165
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 165 223 (accept_3_3 56 165
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 223 (Polychromatic418967fa.accept_9_1_3_7_1_6
  55 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 165 223 (accept_3_3 53 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 165 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 165 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 223 (accept_3_3 50 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 223
  (Polychromatic418967fa.accept_10_8_5_3_1_543 48 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 165 223 (accept_3_3 47 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 165 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 165 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 223 (accept_3_3 44 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 223 (Polychromatic418967fa.accept_19_5_13_14_1_6366 43 165 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 223 (accept_3_3 41 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 165 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 223 (Polychromatic418967fa.accept_12_3_9_7_1_472 39 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 223 (accept_3_3 38 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 165 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 223
  (Polychromatic418967fa.accept_16_4_5_15_1_5083 36 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 165 223 (accept_3_3 35 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 165 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 165 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 223 (accept_3_3 32 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 223 (accept_3_3 29 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 223 (accept_3_3 26 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 223 (Polychromatic418967fa.accept_21_4_18_13_1_10435 25
  165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 223 (accept_3_3 23 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 223 (Polychromatic418967fa.accept_17_4_12_2_1_2349 21 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 223 (accept_3_3 20 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 165 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 223 (accept_3_3 17 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 223 (accept_3_3 14 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 223
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 223 (accept_3_3 11 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 223 (accept_3_3 8 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 223 (accept_3_3 5 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 223 (accept_3_3 2 165 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 165 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 164 223 (Eq.refl Bool.true) (allA_of_3_1
  60 164 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 163 223 (Eq.refl Bool.true) (allA_succ_of_accept 60
  163 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 163 223 (accept_3_3 59 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 163 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 163 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 163 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 163 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 163 223 (accept_3_3 56 163 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 163 223
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 55 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 163 223 (Polychromatic418967fa.accept_19_16_11_14_1_3608 54 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 223 (accept_3_3 53 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 223 (accept_3_3 50 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 223 (accept_3_3 47 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 223 (accept_3_3 44 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 223 (accept_3_3 41 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 223 (accept_3_3 38 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 223 (Polychromatic418967fa.accept_22_15_9_3_1_10071 37 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 223 (accept_3_3 35 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 223 (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 223 (accept_3_3 32 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 223 (accept_3_3 29 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 223
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 163 223 (accept_3_3 26 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 163 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 223 (accept_3_3 23 163 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 22
  163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 223 (accept_3_3 20 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 223 (Polychromatic418967fa.accept_21_19_16_13_1_4099 19 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 223 (accept_3_3 17 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 223 (Polychromatic418967fa.accept_18_16_1_7_1_4083 16 163
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 223
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 223 (accept_3_3 14 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 223 (accept_3_3 11 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 223
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 9 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 223 (accept_3_3 8 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 223 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 223 (accept_3_3 5 163 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 223 (accept_3_3 2 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 162 223
  (Eq.refl Bool.true) (allA_succ_of_accept 61 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 162 223
  (Polychromatic418967fa.accept_11_5_8_3_1_66 60 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 162 223 (accept_3_3 59 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 162 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 162 223 (accept_3_3 56 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 162 223 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 162 223 (accept_3_3 53 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 162 223 (Polychromatic418967fa.accept_25_2_12_23_1_13311 52 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 162 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 223 (accept_3_3 50 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 162 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 223
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 223 (accept_3_3 47 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 223 (Polychromatic418967fa.accept_15_1_12_13_1_944 46 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 223 (accept_3_3 44 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 223 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 223
  (Polychromatic418967fa.accept_19_4_10_14_1_7833 42 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 162 223 (accept_3_3 41 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 162 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 162 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 223 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 162
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 223 (accept_3_3 38 162
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 223
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 162 223 (accept_3_3 35 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 162 223 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 223 (accept_3_3 32 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 223 (Polychromatic418967fa.accept_10_1_2_3_1_1910 31 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 223 (accept_3_3 29 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 223 (Polychromatic418967fa.accept_11_6_8_3_1_2236 28 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 223 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 223 (accept_3_3 26 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 223
  (Polychromatic418967fa.accept_17_7_9_2_1_629 24 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 223 (accept_3_3 23 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 223 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 223 (accept_3_3 20 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 223
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 162 223 (accept_3_3 17 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 162 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 223 (Polychromatic418967fa.accept_10_5_2_3_1_239 15 162
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 223 (accept_3_3 14 162
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9
  13 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 223 (accept_3_3 11 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 223 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 223 (accept_3_3 8 162 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 223 (Polychromatic418967fa.accept_14_7_8_13_1_3161 7 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 223
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 223 (accept_3_3 5 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 223 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 162 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 223 (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 223 (accept_3_3 2 162 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 161 223 (Eq.refl Bool.true)
  (allA_of_3_1 63 161 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 160 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 160 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 160 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 160 223 (accept_3_3 62 160 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 160 223 (Polychromatic418967fa.accept_14_5_6_13_1_3145 61 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 160 223
  (Polychromatic418967fa.accept_17_9_7_2_1_2347 60 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 160 223 (accept_3_3 59 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 160 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 160 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 160 223 (accept_3_3 56 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 160 223 (Polychromatic418967fa.accept_18_1_16_7_1_2897 55 160 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 160 223
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 160 223 (accept_3_3 53 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 160 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 160 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 160 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 160 223 (accept_3_3 50 160 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 160 223
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 160 223 (Polychromatic418967fa.accept_15_3_10_13_1_2605 48 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 160 223 (accept_3_3 47 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 160 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 46 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 160 223 (accept_3_3 44 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 160 223 (Polychromatic418967fa.accept_17_9_7_2_1_2347 43 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 160 223 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 160 223 (accept_3_3 41 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 160 223 (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 160 223 (accept_3_3 38 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 160 223 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 160 223 (Polychromatic418967fa.accept_22_14_6_3_1_6926 36 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 160 223 (accept_3_3 35 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 160 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 160 223 (accept_3_3 32 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 160 223 (Polychromatic418967fa.accept_11_9_6_3_1_1668 31 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 160 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 160 223 (accept_3_3 29 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 223 (Polychromatic418967fa.accept_19_9_8_14_1_10621 28 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 223 (accept_3_3 26 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 160 223 (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 160 223 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 223 (accept_3_3 23 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 160 223 (accept_3_3 20 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 160 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 19 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 160 223 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 223 (accept_3_3 17 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 160 223 (accept_3_3 14 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 160 223 (Polychromatic418967fa.accept_17_13_7_2_1_4562 13 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 223 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 223 (accept_3_3 11 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 160
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 223 (accept_3_3 8 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 223 (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 223 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 223 (accept_3_3 5 160 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 223 (Polychromatic418967fa.accept_15_4_10_13_1_2565 4 160 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 223 (accept_3_3 2 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 1 160 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 159 223
  (Eq.refl Bool.true) (allA_succ_of_accept 64 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 159 223
  (Polychromatic418967fa.accept_11_8_5_3_1_694 63 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 159 223 (accept_3_3 62 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 159 223 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 159 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 223 (accept_3_3 59 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 159 223 (accept_3_3 56 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 159 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 159 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 223 (accept_3_3 53 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 223
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 223 (accept_3_3 50 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 159 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 223 (accept_3_3 47 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 45 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 223 (accept_3_3 44 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 159 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 223 (Polychromatic418967fa.accept_19_4_7_14_1_3537 42 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 223 (accept_3_3 41 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 159 223 (accept_3_3 38 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 159 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 223 (accept_3_3 35 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 223 (accept_3_3 32 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 223 (accept_3_3 29 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 223
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 159 223 (accept_3_3 26 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 159 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 159 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 24 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 223 (accept_3_3 23 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 159 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 223 (accept_3_3 20 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 223 (accept_3_3 17 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 223 (accept_3_3 14 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 223 (accept_3_3 11 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 223 (accept_3_3 8 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 223 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 223 (Polychromatic418967fa.accept_10_6_9_3_1_935 6 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 223 (accept_3_3 5 159 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 223 (accept_3_3 2 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 158 223
  (Eq.refl Bool.true) (allA_of_3_1 66 158 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 157 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 157 223 (accept_3_3 65 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 157 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 157 223
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 63 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 157 223 (accept_3_3 62 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 157 223 (Polychromatic418967fa.accept_13_9_1_2_1_2952 61 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 157 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 223 (accept_3_3 59 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 57 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 223 (accept_3_3 56 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 223 (accept_3_3 53 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 223 (Polychromatic418967fa.accept_14_10_3_13_1_1530 52 157 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 223 (accept_3_3 50 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 223 (Polychromatic418967fa.accept_17_15_4_2_1_8419 49 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 223 (accept_3_3 47 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 223
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 223 (accept_3_3 44 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 223 (Polychromatic418967fa.accept_17_9_4_2_1_2298 43 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 223 (accept_3_3 41 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 223 (Polychromatic418967fa.accept_17_6_4_2_1_5889 40 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 223 (accept_3_3 38 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 223 (accept_3_3 35 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 223 (accept_3_3 32 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 223 (Polychromatic418967fa.accept_27_4_22_7_1_13310 31 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 223 (accept_3_3 29 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 223
  (Polychromatic418967fa.accept_19_8_5_14_1_3586 27 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 223 (accept_3_3 26 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 223 (accept_3_3 23 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 223 (accept_3_3 20 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 223 (accept_3_3 17 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 15 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 223 (accept_3_3 14 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 223 (Polychromatic418967fa.accept_19_13_5_14_1_3530 13 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 223 (accept_3_3 11 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 223 (accept_3_3 8 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 223 (Polychromatic418967fa.accept_21_7_10_13_1_4093 7 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 223 (accept_3_3 5 157 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 157 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 3 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 223 (accept_3_3 2 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 157 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 156
  223 (Eq.refl Bool.true) (allA_succ_of_accept 67 156 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 156 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 156 223 (accept_3_3 65 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 156 223 (Polychromatic418967fa.accept_22_19_2_3_1_13309 63 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 156 223 (accept_3_3 62 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 156 223 (Polychromatic418967fa.accept_16_13_12_15_1_6290 61
  156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 60 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 223 (accept_3_3 59 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 156 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 223 (accept_3_3 56 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 223
  (Polychromatic418967fa.accept_21_12_9_13_1_4091 54 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 156 223 (accept_3_3 53 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 156 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 156 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 156 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 223 (accept_3_3 50 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 223 (Polychromatic418967fa.accept_9_4_3_7_1_296
  49 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 223
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 223 (accept_3_3 47 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 223 (accept_3_3 44 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 223 (accept_3_3 41 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 223 (accept_3_3 38 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 223
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 223 (accept_3_3 35 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 223 (Polychromatic418967fa.accept_11_1_2_3_1_688 34 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 223 (accept_3_3 32 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 223
  (Polychromatic418967fa.accept_24_6_12_7_1_11617 30 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 223 (accept_3_3 29 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 156 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 223 (accept_3_3 26 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 223 (Polychromatic418967fa.accept_7_4_2_6_1_337
  25 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 156 223 (accept_3_3 23 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 156 223 (Polychromatic418967fa.accept_18_3_12_7_1_6728 21 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 223 (accept_3_3 20 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 156 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 156 223 (accept_3_3 17 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 156 223 (Polychromatic418967fa.accept_21_16_9_13_1_4127 16 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 223 (accept_3_3 14 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 223
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 156 223 (accept_3_3 11 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 156 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 156 223 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 156 223 (accept_3_3 8 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 156 223 (accept_3_3 5 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  156 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 156 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 156 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 156 223 (accept_3_3 2 156 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 155 223 (Eq.refl Bool.true)
  (allA_of_3_1 69 155 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 154 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 154 223 (accept_3_3 68 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 154 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 154 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 154 223 (accept_3_3 65
  154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 154 223
  (Polychromatic418967fa.accept_12_4_10_7_1_149 64 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 154 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 154 223 (accept_3_3 62 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 223 (Polychromatic418967fa.accept_9_6_1_7_1_577
  60 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 223 (accept_3_3 59
  154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 223
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 154 223 (accept_3_3 56 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 154 223 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 223
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 54 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 154 223 (accept_3_3 53 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 52 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 223 (accept_3_3 50 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 154 223 (accept_3_3 47 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 154 223 (Polychromatic418967fa.accept_16_14_10_15_1_3969 46 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 223 (accept_3_3 44 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 154 223 (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 154
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 154 223 (accept_3_3 41 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 154 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 154 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 223 (accept_3_3 38 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 223
  (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 154 223 (accept_3_3 35 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 154 223 (Polychromatic418967fa.accept_31_3_30_6_1_13308 34 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 223 (accept_3_3 32
  154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 223
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 154 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 30 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 223 (accept_3_3 29 154 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 154 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 154 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 154 223 (accept_3_3 26 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 154 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 223 (accept_3_3 23 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 154 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 154 223 (accept_3_3 20 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 223 (Polychromatic418967fa.accept_10_9_4_3_1_539 19 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 223 (Polychromatic418967fa.accept_21_18_7_13_1_8801 18 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 223 (accept_3_3 17 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 154
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 154 223 (accept_3_3 14 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 154 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 223 (accept_3_3 11 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 223 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 154 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 154 223 (accept_3_3 8 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  154 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 154 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 223 (accept_3_3 5 154 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 154 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 223 (accept_3_3 2 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 153
  223 (Eq.refl Bool.true) (allA_succ_of_accept 70 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 223
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 69 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 153 223 (accept_3_3 68 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 153 223 (Polychromatic418967fa.accept_19_10_1_14_1_9224 67 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 223 (accept_3_3 65 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 223 (accept_3_3 62 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 223 (Polychromatic418967fa.accept_15_1_3_13_1_2548 61 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 223 (Polychromatic418967fa.accept_13_8_10_2_1_1450 60 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 223 (accept_3_3 59 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 223
  (Polychromatic418967fa.accept_13_5_10_2_1_856 57 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 223 (accept_3_3 56 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 223 (Polychromatic418967fa.accept_13_3_10_2_1_381 55 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 223 (accept_3_3 53 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 223
  (Polychromatic418967fa.accept_11_7_10_3_1_633 51 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 223 (accept_3_3 50 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 223 (Polychromatic418967fa.accept_21_7_6_13_1_10406 49 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 223 (Polychromatic418967fa.accept_19_10_1_14_1_9224 48 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 223 (accept_3_3 47 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 223
  (Polychromatic418967fa.accept_13_6_10_2_1_1449 45 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 223 (accept_3_3 44 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 223 (Polychromatic418967fa.accept_25_18_3_23_1_13307 43 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 223 (accept_3_3 41 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 39 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 223 (accept_3_3 38 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 223 (Polychromatic418967fa.accept_13_11_10_2_1_3840 37 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 223 (Polychromatic418967fa.accept_19_17_1_14_1_6360 36 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 223 (accept_3_3 35 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 223
  (Polychromatic418967fa.accept_22_11_21_3_1_13306 33 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 223 (accept_3_3 32 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 223 (Polychromatic418967fa.accept_13_5_10_2_1_856 31 153 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 223 (accept_3_3 29 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 223 (accept_3_3 26 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 223 (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 223 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 223 (accept_3_3 23 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 223
  (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 223 (accept_3_3 20 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 223 (Polychromatic418967fa.accept_13_6_10_2_1_1449 19 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 223 (accept_3_3 17 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 223 (accept_3_3 14 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 223 (Polychromatic418967fa.accept_19_13_1_14_1_3634 13 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 223 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 223 (accept_3_3 11 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 223
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 9 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 223 (accept_3_3 8 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 223 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 223 (accept_3_3 5 153 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 223 (accept_3_3 2 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 223 (Polychromatic418967fa.accept_15_1_3_13_1_2548 1 153 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72
  152 223 (Eq.refl Bool.true) (allA_of_3_1 72 152 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 151 223
  (Eq.refl Bool.true) (allA_succ_of_accept 72 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 151 223 (accept_3_3 71 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 151 223 (Polychromatic418967fa.accept_15_10_1_13_1_2609 70 151
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 151 223
  (Polychromatic418967fa.accept_21_6_4_13_1_8740 69 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 151 223 (accept_3_3 68 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 151 223 (Polychromatic418967fa.accept_16_3_7_15_1_1130 67 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 151 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 223 (accept_3_3 65 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 223 (Polychromatic418967fa.accept_17_13_15_2_1_654 64 151 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 223
  (Polychromatic418967fa.accept_15_3_1_13_1_1672 63 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 223 (accept_3_3 62 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 223 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 223 (accept_3_3 59 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 223
  (Polychromatic418967fa.accept_15_12_1_13_1_3444 57 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 151 223 (accept_3_3 56 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 151 223 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 223 (Polychromatic418967fa.accept_7_5_4_6_1_167
  54 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 223 (accept_3_3 53
  151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 151 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 223 (accept_3_3 50 151 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 151 223 (Polychromatic418967fa.accept_11_5_8_3_1_66 49 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 223 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  48 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 223 (accept_3_3 47
  151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 223
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 46 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 151 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 151 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 223 (accept_3_3 44 151 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 151 223 (Polychromatic418967fa.accept_16_11_7_15_1_1998 43 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 223
  (Polychromatic418967fa.accept_10_2_1_3_1_233 42 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 223 (accept_3_3 41 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 223 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 223 (accept_3_3 38 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 151 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 223
  (Polychromatic418967fa.accept_13_10_8_2_1_3829 36 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 223 (accept_3_3 35 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 223 (Polychromatic418967fa.accept_19_15_18_14_1_3564 34 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 223 (accept_3_3 32 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 151 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 223 (accept_3_3 29 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 223 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 223 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 223 (accept_3_3 26 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 223 (Polychromatic418967fa.accept_15_10_1_13_1_2609 25 151 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 223 (accept_3_3 23 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 223 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 223 (Polychromatic418967fa.accept_17_4_15_2_1_4551 21 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 223 (accept_3_3 20 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 223
  (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 223 (accept_3_3 17 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 223 (Polychromatic418967fa.accept_19_15_18_14_1_3564 15 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 223 (accept_3_3 14 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 223 (Polychromatic418967fa.accept_17_13_15_2_1_654 13 151
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 223
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 223 (accept_3_3 11 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 223 (accept_3_3 8 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 223 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 223
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 223 (accept_3_3 5 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 223 (Polychromatic418967fa.accept_17_4_15_2_1_4551 4 151 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 223 (accept_3_3 2 151 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 223 (Polychromatic418967fa.accept_19_1_18_14_1_6392 1 151 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 150 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 150 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 72
  150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 150 223 (accept_3_3 71
  150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 150 223
  (Polychromatic418967fa.accept_11_4_7_3_1_289 70 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 150 223 (accept_3_3 68 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 150 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 150 223 (Polychromatic418967fa.accept_9_3_6_7_1_562
  66 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 150 223 (accept_3_3 65
  150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 150 223
  (Polychromatic418967fa.accept_9_1_6_7_1_285 64 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 150 223 (Polychromatic418967fa.accept_18_9_6_7_1_6719 63 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 223 (accept_3_3 62 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 150 223 (Polychromatic418967fa.accept_7_4_3_6_1_340
  60 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 150 223 (accept_3_3 59
  150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 150 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 58 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 223 (accept_3_3 56 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 150 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 223
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 54 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 150 223 (accept_3_3 53 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 150 223 (Polychromatic418967fa.accept_20_12_10_3_1_4537 52 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 150 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 223 (accept_3_3 50 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 150 223 (accept_3_3 47 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 150 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 223 (accept_3_3 44 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 223 (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 223
  (Polychromatic418967fa.accept_20_2_10_3_1_9059 42 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 150 223 (accept_3_3 41 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 150 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 223 (accept_3_3 38 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 223
  (Polychromatic418967fa.accept_24_12_6_7_1_13305 36 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 150 223 (accept_3_3 35 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 150 223 (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 223 (accept_3_3 32 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 223 (Polychromatic418967fa.accept_9_4_6_7_1_286
  31 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 223 (accept_3_3 29 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 223 (Polychromatic418967fa.accept_18_9_6_7_1_6719 27 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 223 (accept_3_3 26 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 223
  (Polychromatic418967fa.accept_19_5_17_14_1_3627 24 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 223 (accept_3_3 23 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 150 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 223 (accept_3_3 20 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 223 (Polychromatic418967fa.accept_9_1_6_7_1_285
  19 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 223 (accept_3_3 17 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 223 (Polychromatic418967fa.accept_11_4_7_3_1_289 15 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 223 (accept_3_3 14 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 223 (accept_3_3 11 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 223 (accept_3_3 8 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 223 (Polychromatic418967fa.accept_16_7_6_15_1_495 7 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 223
  (Polychromatic418967fa.accept_21_6_3_13_1_2742 6 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 223 (accept_3_3 5 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 150 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 223 (accept_3_3 2 150 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 149 223 (Eq.refl
  Bool.true) (allA_of_3_1 75 149 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 148 223 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 148 223 (accept_3_3 74 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 148 223 (Polychromatic418967fa.accept_7_2_1_6_1_173
  72 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 148 223 (accept_3_3 71
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 148 223
  (Polychromatic418967fa.accept_12_10_4_7_1_948 70 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 223 (accept_3_3 68 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 148 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 66
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 148 223 (accept_3_3 65
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 148 223
  (Polychromatic418967fa.accept_9_1_4_7_1_7 64 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 223 (accept_3_3 62 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 148 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 223 (Polychromatic418967fa.accept_9_6_4_7_1_300
  60 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 148 223 (accept_3_3 59
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 148 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 58 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 223 (accept_3_3 56 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 223 (Polychromatic418967fa.accept_7_5_1_6_1_163
  54 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 148 223 (accept_3_3 53
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 148 223
  (Polychromatic418967fa.accept_11_8_5_3_1_694 52 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 223 (accept_3_3 50 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 148 223 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 223 (accept_3_3 47 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 223 (accept_3_3 44 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 223 (accept_3_3 41 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 223 (accept_3_3 38 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 223
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 223 (accept_3_3 35 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 223 (accept_3_3 32 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 223 (Polychromatic418967fa.accept_10_1_8_3_1_947 31 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 223 (accept_3_3 29 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 223 (accept_3_3 26 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 223 (Polychromatic418967fa.accept_10_5_8_3_1_229 25 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 223 (accept_3_3 23 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 22 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 223 (accept_3_3 20 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 148 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 223
  (Polychromatic418967fa.accept_19_18_15_14_1_5017 18 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 148 223 (accept_3_3 17 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 148 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 223 (accept_3_3 14 148 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 223
  (Polychromatic418967fa.accept_18_13_4_7_1_4086 13 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 148 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 223 (accept_3_3 11 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 223 (accept_3_3 8 148
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 223
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 148 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 223 (accept_3_3 5 148 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 148 223 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4 148 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3
  148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 223 (accept_3_3 2 148
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 223 (Polychromatic418967fa.accept_9_1_4_7_1_7
  1 148 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 147 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 147 223 (Polychromatic418967fa.accept_10_5_7_3_1_561
  75 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 147 223 (accept_3_3 74
  147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 223
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 147 223 (Polychromatic418967fa.accept_23_3_9_16_1_13304 72 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 223 (accept_3_3 71 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 147 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 147 223 (accept_3_3 68 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 147 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 67 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 147 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 66 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 223 (accept_3_3 65 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 223
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 63 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 223 (accept_3_3 62 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 223 (Polychromatic418967fa.accept_15_1_12_13_1_944 61 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 223 (accept_3_3 59 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 57 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 223 (accept_3_3 56 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 223 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 223 (accept_3_3 53 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 223 (accept_3_3 50 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 223 (Polychromatic418967fa.accept_14_6_7_13_1_3158 48 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 223 (accept_3_3 47 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 223
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 223 (accept_3_3 44 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 223 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 223 (accept_3_3 41 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 223
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 223 (accept_3_3 38 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 223 (accept_3_3 35 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 223 (accept_3_3 32 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 223 (Polychromatic418967fa.accept_18_12_3_7_1_5373 30 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 223 (accept_3_3 29 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 223
  (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 223 (accept_3_3 26 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 223 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 147 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 223 (accept_3_3 23 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22
  147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 223 (accept_3_3 20 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 223 (accept_3_3 17 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 223 (accept_3_3 14 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 223 (accept_3_3 11 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 223 (accept_3_3 8 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 7 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 223 (accept_3_3 5 147 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 223
  (Polychromatic418967fa.accept_15_3_12_13_1_2549 3 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 223 (accept_3_3 2 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 147 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 146 223 (Eq.refl Bool.true) (allA_of_3_1 78 146 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 145 223
  (Eq.refl Bool.true) (allA_succ_of_accept 78 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 145 223 (accept_3_3 77 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 145 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 145 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 145 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 145 223 (accept_3_3 74 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 145 223 (Polychromatic418967fa.accept_19_16_12_14_1_10640 73 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 223 (accept_3_3 71 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 145 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 223 (accept_3_3 68 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 223 (accept_3_3 65 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 223
  (Polychromatic418967fa.accept_15_3_10_13_1_2605 63 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 145 223 (accept_3_3 62 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 145 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 61 145 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 145 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 223 (accept_3_3 59 145 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 223 (accept_3_3 56 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 223 (Polychromatic418967fa.accept_17_4_9_2_1_9721 55 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 223 (accept_3_3 53 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 52 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 223 (accept_3_3 50 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 223 (accept_3_3 47 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 223
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 223 (accept_3_3 44 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 223 (accept_3_3 41 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 223 (accept_3_3 38 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 223 (accept_3_3 35 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 223 (accept_3_3 32 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 223 (accept_3_3 29 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 223 (Polychromatic418967fa.accept_10_8_5_3_1_543 28 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 223
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 223 (accept_3_3 26 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 223 (accept_3_3 23 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 223 (accept_3_3 20 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 223 (Polychromatic418967fa.accept_15_4_10_13_1_2565 19 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 223 (accept_3_3 17 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 223 (Polychromatic418967fa.accept_15_1_10_13_1_939 16 145 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 223 (accept_3_3 14 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 223 (accept_3_3 11 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 223
  (Polychromatic418967fa.accept_19_9_12_14_1_4966 9 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 223 (accept_3_3 8 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 223 (accept_3_3 5 145 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 145 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 223 (accept_3_3 2 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 144 223 (Eq.refl Bool.true) (allA_succ_of_accept 79 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166
  79 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 144 223
  (Polychromatic418967fa.accept_15_3_9_13_1_1681 78 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 144 223 (accept_3_3 77 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 144 223 (Polychromatic418967fa.accept_28_20_4_27_1_13303 76 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 144 223 (accept_3_3 74 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 144 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 144 223 (accept_3_3 71 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 144 223 (Polychromatic418967fa.accept_21_7_18_13_1_5585 70 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 144 223 (Polychromatic418967fa.accept_10_9_4_3_1_539 69 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 223 (accept_3_3 68 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 67 144
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 144 223 (accept_3_3 65 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 144 223 (Polychromatic418967fa.accept_13_12_1_2_1_845 64 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 223 (Polychromatic418967fa.accept_15_3_9_13_1_1681 63 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 223 (accept_3_3 62 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 223
  (Polychromatic418967fa.accept_19_3_11_14_1_7838 60 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 223 (accept_3_3 59 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 144
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 223 (accept_3_3 56 144
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 223
  (Polychromatic418967fa.accept_13_3_1_2_1_2960 55 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 144 223 (accept_3_3 53 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 144 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166
  51 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 223 (accept_3_3 50
  144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 223
  (Polychromatic418967fa.accept_10_9_4_3_1_539 49 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 144 223 (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 144 223 (accept_3_3 47 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 144 223 (Polychromatic418967fa.accept_11_2_1_3_1_683 46 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 144 223 (accept_3_3 44 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 144 223 (Polychromatic418967fa.accept_19_5_11_14_1_3654 43 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 144 223 (Polychromatic418967fa.accept_13_3_1_2_1_2960 42 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 144 223 (accept_3_3 41 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 223
  (Polychromatic418967fa.accept_10_9_4_3_1_539 39 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 144 223 (accept_3_3 38 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 144 223 (Polychromatic418967fa.accept_19_17_11_14_1_7858 36 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 223 (accept_3_3 35 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 223 (Polychromatic418967fa.accept_15_4_9_13_1_2582 34 144
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 223
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 144 223 (accept_3_3 32 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 144 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 223 (accept_3_3 29 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 223 (Polychromatic418967fa.accept_17_11_8_2_1_3398 28 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 223
  (Polychromatic418967fa.accept_10_7_4_3_1_560 27 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 144 223 (accept_3_3 26 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 144 223 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 144 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 223 (accept_3_3 23 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 223 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 223
  (Polychromatic418967fa.accept_20_1_4_3_1_9085 21 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 144 223 (accept_3_3 20 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 223 (Polychromatic418967fa.accept_15_3_9_13_1_1681 18 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 223 (accept_3_3 17 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 223
  (Polychromatic418967fa.accept_19_15_11_14_1_11940 15 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 144 223 (accept_3_3 14 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 223 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 144 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 223 (accept_3_3 11 144 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 223 (Polychromatic418967fa.accept_7_3_4_6_1_329
  10 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 223 (accept_3_3 8 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 223 (Polychromatic418967fa.accept_13_6_1_2_1_1464 6 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 223 (accept_3_3 5 144 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 223 (Polychromatic418967fa.accept_15_4_9_13_1_2582 4 144 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 223 (accept_3_3 2 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 223 (Polychromatic418967fa.accept_20_1_4_3_1_9085 1 144 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 143 223 (Eq.refl Bool.true) (allA_of_3_1 81 143 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 82 142 223 (Eq.refl Bool.true) (allA_succ_of_accept 81 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9
  81 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 142 223 (accept_3_3 80
  142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 142 223
  (Polychromatic418967fa.accept_13_1_12_2_1_384 79 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 142 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 142 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 142 223 (accept_3_3 77 142 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 142 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 142 223 (accept_3_3 74 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 142 223 (Polychromatic418967fa.accept_17_4_6_2_1_5871 72 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 142 223 (accept_3_3 71 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 142 223 (Polychromatic418967fa.accept_13_5_12_2_1_1423 70 142
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 142 223 (accept_3_3 68 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 142 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 142 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 142 223 (accept_3_3 65 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 142 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 142 223 (accept_3_3 62 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 142 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 142 223 (accept_3_3 59 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 142 223 (Polychromatic418967fa.accept_13_6_12_2_1_4707 58 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 57 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 142 223 (accept_3_3 56 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 142 223 (Polychromatic418967fa.accept_10_5_2_3_1_239 55 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 142 223 (Polychromatic418967fa.accept_15_9_7_13_1_1664 54 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 142 223 (accept_3_3 53 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 142 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 142 223 (accept_3_3 50 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 142 223 (Polychromatic418967fa.accept_21_6_16_13_1_4100 48 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 142 223 (accept_3_3 47 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 142 223 (accept_3_3 44 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 142 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 142 223 (Polychromatic418967fa.accept_13_3_12_2_1_385 42 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 223 (accept_3_3 41 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 223 (Polychromatic418967fa.accept_11_7_10_3_1_633 40 142
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 142 223 (accept_3_3 38 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 142 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 223 (accept_3_3 35 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 142 223 (Polychromatic418967fa.accept_23_11_4_16_1_13302 34 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 142 223 (accept_3_3 32 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 142 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 142 223 (Polychromatic418967fa.accept_13_4_12_2_1_1459 30 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 223 (accept_3_3 29 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 28 142
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 223 (accept_3_3 26 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 223 (accept_3_3 23 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 223 (accept_3_3 20 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 223 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 223 (accept_3_3 17 142 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 16 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 223 (accept_3_3 14 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 223 (Polychromatic418967fa.accept_17_12_6_2_1_2346 12 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 223 (accept_3_3 11 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 223 (accept_3_3 8 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 223 (Polychromatic418967fa.accept_11_7_10_3_1_633 7 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 223 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 223 (accept_3_3 5 142 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 142 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 223 (accept_3_3 2 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 141 223 (Eq.refl Bool.true) (allA_succ_of_accept 82 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27
  82 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 141 223
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 81 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 141 223 (accept_3_3 80 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 141 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 223 (accept_3_3 77 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 141 223 (accept_3_3 74 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 141 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 141 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 223 (accept_3_3 71 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 223
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 69 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 141 223 (accept_3_3 68 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 141 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 67 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 223 (accept_3_3 65 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 141 223 (accept_3_3 62 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 141 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 141 223 (Polychromatic418967fa.accept_16_12_13_15_1_1966 60 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 223 (accept_3_3 59 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 141 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 223 (accept_3_3 56 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 141 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 223 (accept_3_3 53 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 223 (accept_3_3 50 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 141 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 223 (accept_3_3 47 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 223
  (Polychromatic418967fa.accept_19_7_8_14_1_13273 45 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 223 (accept_3_3 44 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 223 (Polychromatic418967fa.accept_13_4_11_2_1_1458 43 141 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 223 (accept_3_3 41 141 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40
  141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 223 (accept_3_3 38 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 223 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 223 (accept_3_3 35 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 223 (accept_3_3 32 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 223 (accept_3_3 29 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 27 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 223 (accept_3_3 26 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 223 (Polychromatic418967fa.accept_19_6_8_14_1_2351 25 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 223 (Polychromatic418967fa.accept_19_5_8_14_1_6384 24 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 223 (accept_3_3 23 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 223 (accept_3_3 20 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 223 (accept_3_3 17 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 15 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 223 (accept_3_3 14 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 223 (accept_3_3 11 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 223 (accept_3_3 8 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 223 (accept_3_3 5 141 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 223 (accept_3_3 2 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 140 223 (Eq.refl Bool.true) (allA_of_3_1 84 140 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 139 223 (Eq.refl Bool.true) (allA_succ_of_accept 84 139 223 (Polychromatic418967fa.accept_8_4_3_7_1_491
  84 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 139 223 (accept_3_3 83
  139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 139 223
  (Polychromatic418967fa.accept_9_1_4_7_1_7 82 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 139 223 (Polychromatic418967fa.accept_11_4_7_3_1_289 81 139 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 223 (accept_3_3 80 139 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 139 223 (Polychromatic418967fa.accept_13_1_9_2_1_1448 79 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 139 223 (accept_3_3 77 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 139 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 76 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 139 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 223 (accept_3_3 74 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 223
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 139 223 (accept_3_3 71 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 139 223 (Polychromatic418967fa.accept_11_4_7_3_1_289 70 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 139 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 223 (accept_3_3 68 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 139 223 (Polychromatic418967fa.accept_16_3_11_15_1_1963 67 139 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 66 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 223 (accept_3_3 65 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 223 (Polychromatic418967fa.accept_13_11_9_2_1_2969 63 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 223 (accept_3_3 62 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 223 (Polychromatic418967fa.accept_23_15_1_16_1_13301 61
  139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 223
  (Polychromatic418967fa.accept_8_4_3_7_1_491 60 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 223 (accept_3_3 59 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 223 (Polychromatic418967fa.accept_13_6_9_2_1_838 58 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 223 (accept_3_3 56 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 223
  (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 223 (accept_3_3 53 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 52 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 223 (accept_3_3 50 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 223 (Polychromatic418967fa.accept_16_1_11_15_1_498 49 139 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 223 (accept_3_3 47 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 223 (Polychromatic418967fa.accept_13_6_9_2_1_838 45 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 223 (accept_3_3 44 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 223 (Polychromatic418967fa.accept_11_10_7_3_1_3679 43 139
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 223 (accept_3_3 41 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 223 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 223 (accept_3_3 38 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 223
  (Polychromatic418967fa.accept_8_4_3_7_1_491 36 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 223 (accept_3_3 35 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 34 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 223 (accept_3_3 32 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 223 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 223 (accept_3_3 29 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 28 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 223 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 223 (accept_3_3 26 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 223 (Polychromatic418967fa.accept_15_10_4_13_1_4506 25 139
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 223 (accept_3_3 23 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 223 (Polychromatic418967fa.accept_17_5_3_2_1_5847 22 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 223 (accept_3_3 20 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 223
  (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 223 (accept_3_3 17 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 223 (Polychromatic418967fa.accept_10_6_9_3_1_935 16 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 223 (accept_3_3 14 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 223 (Polychromatic418967fa.accept_24_13_19_7_1_8129 13 139 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 223
  (Polychromatic418967fa.accept_8_4_3_7_1_491 12 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 223 (accept_3_3 11 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 223 (Polychromatic418967fa.accept_15_9_4_13_1_4482 9 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 223 (accept_3_3 8 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 223 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 139 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 223 (accept_3_3 5 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 223 (Polychromatic418967fa.accept_8_4_3_7_1_491 4 139 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 223 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 223 (accept_3_3 2 139 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 139 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 138 223
  (Eq.refl Bool.true) (allA_succ_of_accept 85 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 138 223
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 84 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 138 223 (accept_3_3 83 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 138 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 138 223 (accept_3_3 80 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 138 223 (Polychromatic418967fa.accept_19_3_5_14_1_3584 79 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 138 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 138 223 (accept_3_3 77 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 138 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 76 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 138 223 (Polychromatic418967fa.accept_10_5_8_3_1_229 75 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 223 (accept_3_3 74 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 223
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 72 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 138 223 (accept_3_3 71 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 138 223 (Polychromatic418967fa.accept_15_10_3_13_1_4480 70 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 223 (accept_3_3 68 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 223
  (Polychromatic418967fa.accept_10_6_8_3_1_930 66 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 138 223 (accept_3_3 65 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 138 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 138 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 63 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 223 (accept_3_3 62 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 223 (accept_3_3 59 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 223 (accept_3_3 56 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 223
  (Polychromatic418967fa.accept_15_9_3_13_1_1686 54 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 223 (accept_3_3 53 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 223 (accept_3_3 50 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 223
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 48 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 223 (accept_3_3 47 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 138 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 223 (accept_3_3 44 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43
  138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 223 (accept_3_3 41 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 223 (accept_3_3 38 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 223 (accept_3_3 35 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 223 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 223 (accept_3_3 32 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 223
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 223 (accept_3_3 29 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 223 (Polychromatic418967fa.accept_15_12_3_13_1_4481 27 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 223 (accept_3_3 26 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 223 (accept_3_3 23 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 223 (accept_3_3 20 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 223 (accept_3_3 17 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 223 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 223 (accept_3_3 14 138 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 223
  (Polychromatic418967fa.accept_15_12_3_13_1_4481 12 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 223 (accept_3_3 11 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 138 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 223 (accept_3_3 8 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 223 (Polychromatic418967fa.accept_13_7_8_2_1_1483
  7 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 223 (accept_3_3 5 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 138 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 223 (Polychromatic418967fa.accept_18_3_12_7_1_6728 3 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 223 (accept_3_3 2 138 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 137 223
  (Eq.refl Bool.true) (allA_of_3_1 87 137 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 136 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 136 223 (accept_3_3 86 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 136 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 136 223 (accept_3_3 83 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 136 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 136 223 (accept_3_3 80 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 136 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 136 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 136 223 (accept_3_3 77 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 136 223 (accept_3_3 74 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 136 223 (Polychromatic418967fa.accept_11_7_4_3_1_302 73 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 136 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 136 223 (accept_3_3 71 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 136 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 223 (accept_3_3 68 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 136 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 136 223 (accept_3_3 65 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 136 223 (Polychromatic418967fa.accept_13_12_6_2_1_1441 64 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 223 (accept_3_3 62 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 136 223 (Polychromatic418967fa.accept_13_9_6_2_1_2200 61 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 136 223 (accept_3_3 59 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 223 (accept_3_3 56 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 223 (Polychromatic418967fa.accept_15_10_1_13_1_2609 55 136 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 223
  (Polychromatic418967fa.accept_19_16_3_14_1_9212 54 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 136 223 (accept_3_3 53 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 136 223 (Polychromatic418967fa.accept_16_4_8_15_1_1113 52 136 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 223 (accept_3_3 50 136 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293
  49 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 223 (accept_3_3 47 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 223 (accept_3_3 44 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 223 (Polychromatic418967fa.accept_13_4_6_2_1_1437 43 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 223 (accept_3_3 41 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 223 (accept_3_3 38 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 223
  (Polychromatic418967fa.accept_13_10_6_2_1_1440 36 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 223 (accept_3_3 35 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 223 (accept_3_3 32 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 223 (accept_3_3 29 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 223 (accept_3_3 26 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 223 (accept_3_3 23 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 223 (accept_3_3 20 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 223 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 223 (accept_3_3 17 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 223 (accept_3_3 14 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 223 (accept_3_3 11 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 10 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 223 (accept_3_3 8 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 223 (accept_3_3 5 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 136 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 223 (accept_3_3 2 136 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 223 (Polychromatic418967fa.accept_13_1_6_2_1_377 1 136 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 135 223
  (Eq.refl Bool.true) (allA_succ_of_accept 88 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 135 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 135 223 (accept_3_3 86 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 135 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 85 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 135 223 (Polychromatic418967fa.accept_19_8_2_14_1_3640 84 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 223 (accept_3_3 83 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 135 223 (accept_3_3 80 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 135 223 (Polychromatic418967fa.accept_21_16_9_13_1_4127 79 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 223 (accept_3_3 77 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 223
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 75 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 223 (accept_3_3 74 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 72 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 223 (accept_3_3 71 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 69 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 223 (accept_3_3 68 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 223 (accept_3_3 65 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 223
  (Polychromatic418967fa.accept_25_13_10_23_1_5981 63 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 223 (accept_3_3 62 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 223 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 135 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 223 (accept_3_3 59 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 58
  135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 223
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 223 (accept_3_3 56 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 223 (Polychromatic418967fa.accept_13_3_5_2_1_1475 55 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 223 (Polychromatic418967fa.accept_16_6_7_15_1_1942 54 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 223 (accept_3_3 53 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 223
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 135 223 (accept_3_3 50 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 135 223 (Polychromatic418967fa.accept_13_10_5_2_1_1477 49 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 223 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 223 (accept_3_3 47 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 223 (accept_3_3 44 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 42 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 223 (accept_3_3 41 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 223
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 223 (accept_3_3 38 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 37 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 223 (accept_3_3 35 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 33 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 223 (accept_3_3 32 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 223 (Polychromatic418967fa.accept_13_4_5_2_1_1436 30 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 223 (accept_3_3 29 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 223
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 223 (accept_3_3 26 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 223 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 223 (accept_3_3 23 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 21 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 223 (accept_3_3 20 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 223 (Polychromatic418967fa.accept_16_3_7_15_1_1130 19 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 223 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 223 (accept_3_3 17 135 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 223
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 223 (accept_3_3 14 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 223 (Polychromatic418967fa.accept_23_13_20_16_1_13300 13 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 223 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 223 (accept_3_3 11 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 223
  (Polychromatic418967fa.accept_12_9_3_7_1_924 9 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 223 (accept_3_3 8 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 223 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 223 (Polychromatic418967fa.accept_16_6_7_15_1_1942 6 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 223 (accept_3_3 5 135 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 223
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 223 (accept_3_3 2 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 223 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 135 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 90 134 223 (Eq.refl Bool.true) (allA_of_3_1 90 134 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 91 133 223 (Eq.refl Bool.true) (allA_succ_of_accept 90 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27
  90 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 133 223 (accept_3_3 89
  133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 133 223
  (Polychromatic418967fa.accept_13_10_3_2_1_4728 88 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 133 223 (Polychromatic418967fa.accept_13_9_3_2_1_399 87 133 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 223 (accept_3_3 86 133 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 133 223 (Polychromatic418967fa.accept_14_1_7_13_1_333 85 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 223
  (Polychromatic418967fa.accept_16_4_5_15_1_5083 84 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 223 (accept_3_3 83 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 223 (Polychromatic418967fa.accept_16_1_5_15_1_2918 81 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 223 (accept_3_3 80 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 223 (Polychromatic418967fa.accept_11_2_1_3_1_683 79 133
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 78 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 223 (accept_3_3 77 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 223 (Polychromatic418967fa.accept_13_11_3_2_1_863 76 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 223 (Polychromatic418967fa.accept_13_10_3_2_1_4728 75 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 223 (accept_3_3 74 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 223 (Polychromatic418967fa.accept_17_5_14_2_1_4568 73 133
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 223
  (Polychromatic418967fa.accept_20_12_13_3_1_13299 72 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 133 223 (accept_3_3 71 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 133 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 223 (Polychromatic418967fa.accept_21_6_7_13_1_7199 69 133
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 223 (accept_3_3 68 133
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 223
  (Polychromatic418967fa.accept_17_16_14_2_1_5841 67 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 223 (accept_3_3 65 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 223 (Polychromatic418967fa.accept_13_12_3_2_1_1470 64 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 223
  (Polychromatic418967fa.accept_13_11_3_2_1_863 63 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 133 223 (accept_3_3 62 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 223 (Polychromatic418967fa.accept_13_9_3_2_1_399 61 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 223 (Polychromatic418967fa.accept_21_18_7_13_1_8801 60 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 223 (accept_3_3 59 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 223
  (Polychromatic418967fa.accept_11_2_1_3_1_683 57 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 223 (accept_3_3 56 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 223 (Polychromatic418967fa.accept_22_11_1_3_1_10096 55 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 223 (accept_3_3 53 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 223 (Polychromatic418967fa.accept_16_4_5_15_1_5083 52 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 223
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 133 223 (accept_3_3 50 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 133 223 (Polychromatic418967fa.accept_13_10_3_2_1_4728 49 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 133 223 (Polychromatic418967fa.accept_13_9_3_2_1_399 48 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 223 (accept_3_3 47 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 223
  (Polychromatic418967fa.accept_24_21_13_7_1_8122 45 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 133 223 (accept_3_3 44 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 133 223 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 133 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 223 (accept_3_3 41 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 223 (Polychromatic418967fa.accept_13_1_3_2_1_1429
  40 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 223
  (Polychromatic418967fa.accept_17_5_14_2_1_4568 39 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 223 (accept_3_3 38 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 223 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 223 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 223 (accept_3_3 35 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 223
  (Polychromatic418967fa.accept_16_1_5_15_1_2918 33 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 223 (accept_3_3 32 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 223 (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 223 (accept_3_3 29 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 223 (Polychromatic418967fa.accept_20_8_13_3_1_9081 28 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 223
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 27 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 223 (accept_3_3 26 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 223 (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 223 (Polychromatic418967fa.accept_11_2_1_3_1_683 24 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 223 (accept_3_3 23 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 223
  (Polychromatic418967fa.accept_20_1_13_3_1_11838 21 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 133 223 (accept_3_3 20 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 133 223 (Polychromatic418967fa.accept_21_19_7_13_1_7189 19 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 223 (accept_3_3 17
  133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 223
  (Polychromatic418967fa.accept_17_16_14_2_1_5841 16 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 223 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 223 (accept_3_3 14 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 223 (Polychromatic418967fa.accept_11_2_1_3_1_683 13 133
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 223
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 223 (accept_3_3 11 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 223 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 223 (accept_3_3 8 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 223 (Polychromatic418967fa.accept_28_7_21_27_1_13298 7 133 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 223
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 223 (accept_3_3 5 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 223 (Polychromatic418967fa.accept_16_4_5_15_1_5083 4 133 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 223 (Polychromatic418967fa.accept_17_3_14_2_1_646 3 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 223 (accept_3_3 2 133 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 223 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 133 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 132 223
  (Eq.refl Bool.true) (allA_succ_of_accept 91 132 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 132 223
  (Polychromatic418967fa.accept_20_10_12_3_1_6003 90 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 132 223 (accept_3_3 89 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 132 223 (Polychromatic418967fa.accept_16_8_4_15_1_2941 88 132 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 132 223 (Polychromatic418967fa.accept_21_3_6_13_1_8756 87 132
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 132 223 (accept_3_3 86 132
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 132 223
  (Polychromatic418967fa.accept_9_4_6_7_1_286 85 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 132 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 84 132 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 132 223 (accept_3_3 83 132 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 82 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 132 223 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  81 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 223 (accept_3_3 80
  132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 223
  (Polychromatic418967fa.accept_19_3_18_14_1_5020 79 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 132 223 (Polychromatic418967fa.accept_15_3_12_13_1_2549 78 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 223 (accept_3_3 77 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 76 132 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 223
  (Polychromatic418967fa.accept_8_3_4_7_1_475 75 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 132 223 (accept_3_3 74 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 73 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 132 223 (Polychromatic418967fa.accept_16_8_4_15_1_2941 72 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 132 223 (accept_3_3 71 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 223 (Polychromatic418967fa.accept_15_10_12_13_1_2585 70
  132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 223
  (Polychromatic418967fa.accept_16_5_4_15_1_1102 69 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 132 223 (accept_3_3 68 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 132 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 67 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 132 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 66 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 132 223 (accept_3_3 65 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 223
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 63 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 132 223 (accept_3_3 62 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 132 223 (Polychromatic418967fa.accept_10_1_2_3_1_1910 61 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 132 223 (Polychromatic418967fa.accept_16_12_4_15_1_5091 60 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 132 223 (accept_3_3 59 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 132 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 132 223 (accept_3_3 56 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 132 223 (Polychromatic418967fa.accept_14_12_6_13_1_3173 54 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 132 223 (accept_3_3 53 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 223 (Polychromatic418967fa.accept_17_1_13_2_1_7086 52 132
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 223
  (Polychromatic418967fa.accept_8_3_4_7_1_475 51 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 132 223 (accept_3_3 50 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 132 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 48 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 132 223 (accept_3_3 47 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 223
  (Polychromatic418967fa.accept_10_5_2_3_1_239 45 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 132 223 (accept_3_3 44 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 132 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 132 223 (Polychromatic418967fa.accept_19_4_18_14_1_3630 42 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 223 (accept_3_3 41 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 132 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 132 223 (accept_3_3 38 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 132 223 (Polychromatic418967fa.accept_21_15_6_13_1_8776 36 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 132 223 (accept_3_3 35 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 223 (Polychromatic418967fa.accept_19_15_18_14_1_3564 34
  132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 223
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 132 223 (accept_3_3 32 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 132 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 132 223 (accept_3_3 29 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 223
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 132 223 (accept_3_3 26 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 132 223 (Polychromatic418967fa.accept_10_5_2_3_1_239 25 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 132 223 (Polychromatic418967fa.accept_16_8_4_15_1_2941 24 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 132 223 (accept_3_3 23 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 132 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 223
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 132 223 (accept_3_3 20 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 132 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 132 223 (Polychromatic418967fa.accept_15_3_12_13_1_2549 18 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 132 223 (accept_3_3 17 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 223 (Polychromatic418967fa.accept_15_1_12_13_1_944 16 132
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 223
  (Polychromatic418967fa.accept_10_5_2_3_1_239 15 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 132 223 (accept_3_3 14 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 132 223 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 132 223 (accept_3_3 11 132 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 223
  (Polychromatic418967fa.accept_18_9_6_7_1_6719 9 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 132 223 (accept_3_3 8 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  132 223 (Polychromatic418967fa.accept_14_7_6_13_1_4111 7 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 132 223 (Polychromatic418967fa.accept_17_6_13_2_1_4549 6 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 132 223 (accept_3_3 5 132 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 223 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 132 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 223
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 132 223 (accept_3_3 2 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  132 223 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 132
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 131 223
  (Eq.refl Bool.true) (allA_of_3_1 93 131 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 130 223 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 130 223 (accept_3_3 92 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 130 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 91 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 130 223
  (Polychromatic418967fa.accept_21_6_4_13_1_8740 90 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 130 223 (accept_3_3 89 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 130 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 88 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 130 223 (accept_3_3 86 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 130 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 84 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 130 223 (accept_3_3 83 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 130 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 82 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 130 223 (accept_3_3 80 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 130 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 130 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 78 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 130 223 (accept_3_3 77 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 130 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 76 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 130 223 (accept_3_3 74 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 223
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 130 223 (accept_3_3 71 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 130 223 (Polychromatic418967fa.accept_18_16_4_7_1_2927 70 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 223 (accept_3_3 68 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 130 223 (Polychromatic418967fa.accept_16_3_2_15_1_7367 67 130 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 130 223 (accept_3_3 65 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 130 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 223 (accept_3_3 62 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 130 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 130 223 (accept_3_3 59 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 130 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 223 (accept_3_3 56 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 130 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 130 223
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 223 (accept_3_3 53 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 130 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 130 223 (accept_3_3 50 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 223
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 223 (accept_3_3 47 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 223 (accept_3_3 44 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 223 (Polychromatic418967fa.accept_17_9_11_2_1_5894 43 130 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 223
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 223 (accept_3_3 41 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 223 (accept_3_3 38 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 223
  (Polychromatic418967fa.accept_19_17_16_14_1_10604 36 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 130 223 (accept_3_3 35 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 130 223 (Polychromatic418967fa.accept_15_4_10_13_1_2565 34 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 223 (accept_3_3 32
  130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 223
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 130 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 130 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 223 (accept_3_3 29 130 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 130 223 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 27
  130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 223 (accept_3_3 26
  130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 130 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 130 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 223 (accept_3_3 23 130 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 130 223 (Polychromatic418967fa.accept_19_3_16_14_1_6369 22 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 223 (accept_3_3 20 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 223 (Polychromatic418967fa.accept_15_3_10_13_1_2605 18 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 223 (accept_3_3 17 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 223 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 130 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 223 (accept_3_3 14 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 223 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 223 (accept_3_3 11 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 223 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 223 (accept_3_3 8 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 223 (Polychromatic418967fa.accept_20_7_10_3_1_949 7 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 223 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 223 (accept_3_3 5 130 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 223 (Polychromatic418967fa.accept_12_4_10_7_1_149 4 130 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 223 (accept_3_3 2 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 129
  223 (Eq.refl Bool.true) (allA_succ_of_accept 94 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 94 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 129 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 93 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 129 223 (accept_3_3 92 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 129 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 91 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 223 (accept_3_3 89 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 87 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 223 (accept_3_3 86 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 85 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 223 (Polychromatic418967fa.accept_10_4_9_3_1_1907 84 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 223 (accept_3_3 83 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 129 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 223 (accept_3_3 80 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 223 (accept_3_3 77 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 75 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 223 (accept_3_3 74 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 73 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 223 (accept_3_3 71 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 69 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 223 (accept_3_3 68 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 223 (accept_3_3 65 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 63 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 223 (accept_3_3 62 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 223 (Polychromatic418967fa.accept_11_6_8_3_1_2236 61 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 223 (accept_3_3 59 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 223
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 57 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 223 (accept_3_3 56 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 223 (accept_3_3 53 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 223 (accept_3_3 50 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 223 (Polychromatic418967fa.accept_15_3_9_13_1_1681 48 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 223 (accept_3_3 47 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 223
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 45 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 223 (accept_3_3 44 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 223 (Polychromatic418967fa.accept_13_4_12_2_1_1459 43 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 223 (accept_3_3 41 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 223
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 223 (accept_3_3 38 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 223 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 223 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 223 (accept_3_3 35 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 223 (accept_3_3 32 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 223 (accept_3_3 29 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 223
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 223 (accept_3_3 26 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 223 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 223 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 223 (accept_3_3 23 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 223
  (Polychromatic418967fa.accept_16_5_1_15_1_3922 21 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 223 (accept_3_3 20 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 223 (accept_3_3 17 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 223
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 223 (accept_3_3 14 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 223 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 223 (Polychromatic418967fa.accept_17_12_10_2_1_5835 12 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 223 (accept_3_3 11 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 223
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 223 (accept_3_3 8 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 223 (Polychromatic418967fa.accept_15_7_9_13_1_3451 7 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 223 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 223 (accept_3_3 5 129 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 223 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 223
  (Polychromatic418967fa.accept_12_3_9_7_1_472 3 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 223 (accept_3_3 2 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 223 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 129 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 128
  223 (Eq.refl Bool.true) (allA_of_3_1 96 128 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 97 127 223
  (Eq.refl Bool.true) (allA_succ_of_accept 96 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 127 223 (accept_3_3 95 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 94 127 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 127 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 127 223 (accept_3_3 92 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 127 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 91 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 127 223 (Polychromatic418967fa.accept_13_12_10_2_1_1451 90 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 223 (accept_3_3 89 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 223 (Polychromatic418967fa.accept_18_16_1_7_1_4083 88 127
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 87 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 127 223 (accept_3_3 86 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 85 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 84 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 223 (accept_3_3 83 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 223
  (Polychromatic418967fa.accept_13_3_10_2_1_381 81 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 223 (accept_3_3 80 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 79 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 78 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 223 (accept_3_3 77 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 223 (accept_3_3 74 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 223 (Polychromatic418967fa.accept_13_8_10_2_1_1450 73 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 223 (accept_3_3 71 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 223 (Polychromatic418967fa.accept_13_5_10_2_1_856 70 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 69 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 223 (accept_3_3 68 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 66 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 223 (accept_3_3 65 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 223 (Polychromatic418967fa.accept_10_4_7_3_1_54 64 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 223
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 223 (accept_3_3 62 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 223 (accept_3_3 59 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 223 (accept_3_3 56 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 223 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 223 (accept_3_3 53 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 223 (Polychromatic418967fa.accept_11_8_6_3_1_661 52 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 223 (accept_3_3 50 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 223 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 223 (accept_3_3 47 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 46 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 223
  (Polychromatic418967fa.accept_10_5_7_3_1_561 45 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 223 (accept_3_3 44 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 223 (Polychromatic418967fa.accept_19_5_13_14_1_6366 43 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 223 (accept_3_3 41 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 223 (accept_3_3 38 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 223 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 223 (accept_3_3 35 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 223 (Polychromatic418967fa.accept_10_4_7_3_1_54 34 127 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 223
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 223 (accept_3_3 32 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 223 (accept_3_3 29 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 223 (Polychromatic418967fa.accept_17_11_8_2_1_3398 28 127 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 223
  (Polychromatic418967fa.accept_17_10_8_2_1_8411 27 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 223 (accept_3_3 26 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 223 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 223 (accept_3_3 23 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 223 (accept_3_3 20 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 223 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 223 (accept_3_3 17 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 223 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 223
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 223 (accept_3_3 14 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 223 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 223 (accept_3_3 11 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 223 (Polychromatic418967fa.accept_17_10_8_2_1_8411 10 127 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 223
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 223 (accept_3_3 8 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 223 (Polychromatic418967fa.accept_14_7_1_13_1_357 7 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 223 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 223 (accept_3_3 5 127 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 223 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 223
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 223 (accept_3_3 2 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 223 (Polychromatic418967fa.accept_19_1_13_14_1_3509 1 127 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  126 223 (Eq.refl Bool.true) (allA_succ_of_accept 97 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 97 126 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 126 223
  (Polychromatic418967fa.accept_11_8_5_3_1_694 96 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 126 223 (accept_3_3 95 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 126 223 (Polychromatic418967fa.accept_13_3_9_2_1_1486 94 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 93 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 126 223 (accept_3_3 92 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 126 223 (Polychromatic418967fa.accept_25_16_1_23_1_13297 91 126 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 126 223
  (Polychromatic418967fa.accept_16_10_14_15_1_2933 90 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 126 223 (accept_3_3 89 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 126 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 88 126 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 87 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 223 (accept_3_3 86 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9
  85 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 126 223
  (Polychromatic418967fa.accept_13_6_9_2_1_838 84 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 126 223 (accept_3_3 83 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 126 223 (Polychromatic418967fa.accept_15_7_6_13_1_936 82 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 223 (accept_3_3 80 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 126 223 (Polychromatic418967fa.accept_10_9_6_3_1_545 79 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 223
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 78 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 126 223 (accept_3_3 77 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 126 223 (Polychromatic418967fa.accept_13_11_9_2_1_2969 76 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 126 223 (Polychromatic418967fa.accept_22_9_16_3_1_13296 75 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 223 (accept_3_3 74 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 126 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 126 223
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 72 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 126 223 (accept_3_3 71 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 126 223 (Polychromatic418967fa.accept_13_5_9_2_1_1489 70 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 223 (accept_3_3 68 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 67 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 126 223
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 66 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 126 223 (accept_3_3 65 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 126 223 (Polychromatic418967fa.accept_15_4_6_13_1_956 64 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 126 223 (Polychromatic418967fa.accept_11_8_5_3_1_694 63 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 223 (accept_3_3 62 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 126 223
  (Polychromatic418967fa.accept_17_9_7_2_1_2347 60 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 126 223 (accept_3_3 59 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 126 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 58 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 223 (accept_3_3 56 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 223 (Polychromatic418967fa.accept_13_3_9_2_1_1486 55 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 223
  (Polychromatic418967fa.accept_19_16_12_14_1_10640 54 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 223 (accept_3_3 53 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 126 223 (Polychromatic418967fa.accept_11_8_5_3_1_694 52 126 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 223 (Polychromatic418967fa.accept_19_13_12_14_1_9217 51
  126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 223 (accept_3_3 50
  126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 126 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 126 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 223 (accept_3_3 47 126 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 126 223 (Polychromatic418967fa.accept_13_7_9_2_1_2167 46 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 126 223 (accept_3_3 44 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 126 223 (Polychromatic418967fa.accept_17_9_7_2_1_2347 43 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 126 223 (Polychromatic418967fa.accept_13_3_9_2_1_1486 42 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 126 223 (accept_3_3 41 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 223 (Polychromatic418967fa.accept_13_1_9_2_1_1448 40 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 223
  (Polychromatic418967fa.accept_10_9_6_3_1_545 39 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 223 (accept_3_3 38 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 223 (Polychromatic418967fa.accept_16_4_14_15_1_6331 36 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 223 (accept_3_3 35 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 223 (Polychromatic418967fa.accept_15_4_6_13_1_956 34 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 126 223 (accept_3_3 32 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 126 223 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 126 223 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 126 223 (accept_3_3 29 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 223
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 126 223 (accept_3_3 26 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 126 223 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 126 223 (accept_3_3 23 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 223 (Polychromatic418967fa.accept_15_7_6_13_1_936 22 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 126 223 (accept_3_3 20 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 126 223 (Polychromatic418967fa.accept_10_9_6_3_1_545 19 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 126 223 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 126 223 (accept_3_3 17 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 223 (Polychromatic418967fa.accept_13_3_9_2_1_1486 16 126
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 223
  (Polychromatic418967fa.accept_17_15_7_2_1_2303 15 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 126 223 (accept_3_3 14 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 126 223 (Polychromatic418967fa.accept_17_12_7_2_1_4561 12 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 223 (accept_3_3 11 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 223 (Polychromatic418967fa.accept_16_10_14_15_1_2933 10
  126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 223
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 223 (accept_3_3 8 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  126 223 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 126 223 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 126 223 (accept_3_3 5 126 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 223 (Polychromatic418967fa.accept_15_4_6_13_1_956 4 126 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 223
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 126 223 (accept_3_3 2 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  126 223 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 126
  223)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 99
  125 223 (Eq.refl Bool.true) (allA_of_3_1 99 125 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 100 124 223
  (Eq.refl Bool.true) (allA_succ_of_accept 99 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 99 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 124 223 (accept_3_3 98 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 124 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 97 124
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 124 223
  (Polychromatic418967fa.accept_13_5_7_2_1_852 96 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 95 124 223 (accept_3_3 95 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  94 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 94 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 93 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 93 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 124 223 (accept_3_3 92 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 124 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 91 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 124 223
  (Polychromatic418967fa.accept_14_6_12_13_1_3180 90 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 124 223 (accept_3_3 89 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 88 124 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 124 223 (accept_3_3 86 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 85
  124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 124 223
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 84 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 124 223 (accept_3_3 83 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 82 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 124 223 (accept_3_3 80 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 124 223 (Polychromatic418967fa.accept_10_9_4_3_1_539 79 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 124 223
  (Polychromatic418967fa.accept_7_1_5_6_1_59 78 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 124 223 (accept_3_3 77 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 124 223 (Polychromatic418967fa.accept_14_6_12_13_1_3180 76 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 124 223 (accept_3_3 74 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 124 223 (Polychromatic418967fa.accept_13_8_7_2_1_2988 73 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 124 223
  (Polychromatic418967fa.accept_16_8_12_15_1_2005 72 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 124 223 (accept_3_3 71 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 70 124 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 124 223 (accept_3_3 68 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344
  67 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 124 223
  (Polychromatic418967fa.accept_15_6_4_13_1_403 66 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 124 223 (accept_3_3 65 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 124 223 (accept_3_3 62 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 124 223 (Polychromatic418967fa.accept_13_9_7_2_1_3869 61 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 223
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 124 223 (accept_3_3 59 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 58 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 223 (accept_3_3 56 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 223 (Polychromatic418967fa.accept_15_10_4_13_1_4506 55 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 223
  (Polychromatic418967fa.accept_15_9_4_13_1_4482 54 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 223 (accept_3_3 53 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 223 (Polychromatic418967fa.accept_16_4_12_15_1_6289 52 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 223 (accept_3_3 50 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 223 (Polychromatic418967fa.accept_10_9_4_3_1_539 49 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 223
  (Polychromatic418967fa.accept_13_9_7_2_1_3869 48 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 124 223 (accept_3_3 47 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 223 (accept_3_3 44 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 124 223
  (Polychromatic418967fa.accept_19_4_10_14_1_7833 42 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 124 223 (accept_3_3 41 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 124 223 (Polychromatic418967fa.accept_15_10_4_13_1_4506 40 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 223 (Polychromatic418967fa.accept_6_3_4_1_1_8 39
  124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 223 (accept_3_3 38
  124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 223
  (Polychromatic418967fa.accept_10_7_4_3_1_560 37 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 124 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 223 (accept_3_3 35 124 223 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948 34 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 223 (accept_3_3 32 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 223 (Polychromatic418967fa.accept_13_5_7_2_1_852 31 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 223 (Polychromatic418967fa.accept_23_7_9_16_1_13295 30 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 223 (accept_3_3 29 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 223 (Polychromatic418967fa.accept_21_7_19_13_1_7164 28 124
  223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 223 (accept_3_3 26 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 223 (Polychromatic418967fa.accept_15_9_4_13_1_4482 24 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 223 (accept_3_3 23 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 223 (accept_3_3 20 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 223 (Polychromatic418967fa.accept_8_3_4_7_1_475 19 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 223 (accept_3_3 17 124 223 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 223 (Polychromatic418967fa.accept_17_16_5_2_1_9724 16 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 223 (accept_3_3 14 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 223 (Polychromatic418967fa.accept_16_13_12_15_1_6290 13 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 223 (Polychromatic418967fa.accept_19_12_10_14_1_6353 12 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 223 (accept_3_3 11 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 223 (Polychromatic418967fa.accept_12_10_4_7_1_948
  10 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 223 (accept_3_3 8 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 223 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 223 (Polychromatic418967fa.accept_14_6_12_13_1_3180 6 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 223 (accept_3_3 5 124 223 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 223 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 124 223
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 223
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 223 (accept_3_3 2 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 223 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 124 223 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  223))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_223_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


