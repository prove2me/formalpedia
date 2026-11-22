-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch205
-- name    : Polychromatic418967fa_Branch205
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:23.374184+00:00
-- url     : https://prove2.me/theorems/f894975c-f3b5-4f1e-aa10-1beb61063e7a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch205_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_205 : allB 205 205 :=
  allB_succ' 2 204 205 (Eq.refl Bool.true) (allA_succ_of_accept 1 204 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1
  204 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 205)) (allB_succ' 3 203 205
  (Eq.refl Bool.true) (allA_of_3_1 3 203 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 202 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 205 (accept_3_3 2 202 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 202 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 205)))) (allB_succ' 5 201 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 201 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 201 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 205 (accept_3_3 2 201 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 1
  201 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 205))))) (allB_succ' 6 200 205
  (Eq.refl Bool.true) (allA_of_3_1 6 200 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 199 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 199 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 205 (accept_3_3 5 199 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 199 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 199 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 205 (accept_3_3 2 199 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 199 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 205))))))) (allB_succ' 8 198 205 (Eq.refl Bool.true) (allA_succ_of_accept 7 198 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 198 205 (Polychromatic418967fa.accept_13_6_3_10_1_698 6 198 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 205 (accept_3_3 5 198 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 198 205 (Polychromatic418967fa.accept_14_4_2_9_1_2092 4 198 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 198 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3
  198 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 205 (accept_3_3 2 198
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 205
  (Polychromatic418967fa.accept_19_1_8_15_1_3786 1 198 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 205)))))))) (allB_succ' 9 197 205 (Eq.refl Bool.true) (allA_of_3_1 9 197 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 10 196 205 (Eq.refl Bool.true) (allA_succ_of_accept 9 196 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 205 (accept_3_3 8 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  196 205 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 196 205 (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 196 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 205 (accept_3_3 5 196 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 205 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 196 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 196 205 (accept_3_3 2 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  196 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 196 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 196 205)))))))))) (allB_succ' 11 195 205 (Eq.refl Bool.true) (allA_succ_of_gcd 10 195 205 5 2 39
  41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 195 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 205 (accept_3_3 8 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 205 (Polychromatic418967fa.accept_17_7_8_1_1_1373 7 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 205 5 1 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  195 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 205 (accept_3_3 2 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 195 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 205))))))))))) (allB_succ' 12 194 205 (Eq.refl Bool.true) (allA_of_3_1 12 194 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 193 205 (Eq.refl Bool.true) (allA_succ_of_accept 12 193 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 205 (accept_3_3 11 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 205 (Polychromatic418967fa.accept_16_9_1_13_1_1850 9 193 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 205 (accept_3_3 8 193 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 193 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 205 (accept_3_3 5 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 193 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 193 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 205 (accept_3_3 2 193 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 205))))))))))))) (allB_succ' 14 192 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 192 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 205 (Polychromatic418967fa.accept_7_5_3_2_1_249
  12 192 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 205 (accept_3_3 11
  192 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 205
  (Polychromatic418967fa.accept_9_1_3_7_1_6 10 192 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 192 205 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 192 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 192 205 (accept_3_3 8 192 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 192 205 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 192 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 6
  192 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 205 (accept_3_3 5 192
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 205
  (Polychromatic418967fa.accept_9_4_3_7_1_296 4 192 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 192 205 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 192 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 192 205 (accept_3_3 2 192 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 192 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 192 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 205)))))))))))))) (allB_succ' 15 191 205 (Eq.refl Bool.true)
  (allA_of_3_1 15 191 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 190 205 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 190 205 5 3 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 190 205 (accept_3_3 14 190 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 190 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 190 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 190 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 190 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 190 205 (accept_3_3 11 190 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 205 5 2 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 190 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 205 (accept_3_3 8 190 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  190 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 190 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 190 205 5 1 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 190 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 190 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 205 (accept_3_3 2 190 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 205 (Polychromatic418967fa.accept_14_1_8_9_1_1312
  1 190 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 205)))))))))))))))) (allB_succ'
  17 189 205 (Eq.refl Bool.true) (allA_succ_of_accept 16 189 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 189 205 (accept_3_3 14 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 189 205 (Polychromatic418967fa.accept_17_13_2_1_1_4483 13 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 189 205 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 189 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 205 (accept_3_3 11 189 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 189 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 205
  (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 189 205 (accept_3_3 8 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  189 205 (Polychromatic418967fa.accept_19_7_18_15_1_5061 7 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 189 205 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 189 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 205 (accept_3_3 5 189 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 189 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 205 (accept_3_3 2 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 205 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 189 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 205))))))))))))))))) (allB_succ' 18 188 205 (Eq.refl Bool.true) (allA_of_3_1 18 188 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 187 205 (Eq.refl Bool.true) (allA_succ_of_accept 18 187 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 205 (accept_3_3 17 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 205 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 187 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 205 (accept_3_3 14 187 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 205 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 187
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 205
  (Polychromatic418967fa.accept_10_2_7_5_1_605 12 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 205 (accept_3_3 11 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 205 (Polychromatic418967fa.accept_20_9_7_5_1_2114 9 187 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 205 (accept_3_3 8 187 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 205 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 187 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 205 (accept_3_3 5 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 187 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 187 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 205 (accept_3_3 2 187 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 187 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 205))))))))))))))))))) (allB_succ' 20 186 205
  (Eq.refl Bool.true) (allA_succ_of_accept 19 186 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 186 205
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 186 205 (accept_3_3 17 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 186 205 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 186 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 205 (accept_3_3 14 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 186 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 186 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 186 205 (accept_3_3 11 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 186 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 186 205 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 205 (accept_3_3 8 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 186 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 186 205 (accept_3_3 5 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  186 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 186 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 186 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 205 (accept_3_3 2 186 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 205)))))))))))))))))))) (allB_succ' 21 185 205
  (Eq.refl Bool.true) (allA_of_3_1 21 185 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 184 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 205 (accept_3_3 20 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 184 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 184 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 205
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 205 (accept_3_3 17 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 205 (accept_3_3 14 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 205 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 184 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 205
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 205 (accept_3_3 11 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 205 (accept_3_3 8 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 205 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 184 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 205 (accept_3_3 5 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 205 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 184 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 205 (accept_3_3 2 184 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 205)))))))))))))))))))))) (allB_succ' 23 183 205
  (Eq.refl Bool.true) (allA_succ_of_accept 22 183 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 205 (accept_3_3 20 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 205 (accept_3_3 17 183 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 205 (accept_3_3 14 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 183 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 205 (accept_3_3 11 183 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 205 (accept_3_3 8 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 205 (accept_3_3 5 183 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 205
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 205 (accept_3_3 2 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 183 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 205))))))))))))))))))))))) (allB_succ' 24 182 205 (Eq.refl Bool.true) (allA_of_3_1 24 182
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 181 205 (Eq.refl Bool.true) (allA_succ_of_accept 24 181
  205 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 205 (accept_3_3 23 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 205 (accept_3_3 20 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 205 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 181 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 205
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 205 (accept_3_3 17 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 205 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 205 (accept_3_3 14 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 181 205 (accept_3_3 11 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 181 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 205 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 205 (accept_3_3 8 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 205 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 181 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 205 (accept_3_3 5 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 181 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 205 (accept_3_3 2 181 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 205))))))))))))))))))))))))) (allB_succ' 26 180 205
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 180 205 5 5 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 180 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 180 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 180 205 (accept_3_3 23 180 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 205 (Polychromatic418967fa.accept_16_6_4_13_1_3841 22 180
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 205
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 205 5 4 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 205 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 180 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 180 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 180 205 (accept_3_3 17 180 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 205
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 180 205 5 3 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 180 205 (accept_3_3 14 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 205 (Polychromatic418967fa.accept_19_13_9_15_1_11989 13 180 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 205
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 180 205 (accept_3_3 11 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 205 5 2 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 180 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 180 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 205 (accept_3_3 8 180 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 180 205 (Polychromatic418967fa.accept_14_7_12_9_1_2926 7 180 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 205
  (Polychromatic418967fa.accept_16_6_4_13_1_3841 6 180 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 180 205 5 1 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 180 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 180 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 205 (accept_3_3 2 180 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1
  180 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 205))))))))))))))))))))))))))
  (allB_succ' 27 179 205 (Eq.refl Bool.true) (allA_of_3_1 27 179 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 28 178 205 (Eq.refl Bool.true) (allA_succ_of_accept 27 178 205 (Polychromatic418967fa.accept_4_3_2_1_1_50
  27 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 205 (accept_3_3 26
  178 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 178 205
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 205 (Polychromatic418967fa.accept_17_7_8_1_1_1373 24 178 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 205 (accept_3_3 23 178 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 178 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 205 (accept_3_3 20 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 205 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 178 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 205 (accept_3_3 17 178 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 178
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 205 (accept_3_3 14 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 178 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 205 (accept_3_3 11 178 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 205 (Polychromatic418967fa.accept_20_10_18_5_1_11942 10 178 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 205 (accept_3_3 8 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 178 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 205 (accept_3_3 5 178 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 178 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 205 (accept_3_3 2 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 178 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 205)))))))))))))))))))))))))))) (allB_succ' 29 177 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 28 177 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 205 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 177
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 205 (accept_3_3 26 177
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 205
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 177 205 (Polychromatic418967fa.accept_13_11_8_10_1_676 24 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 205 (accept_3_3 23 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 177 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 177 205 (accept_3_3 20 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 177 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 177 205 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 205 (accept_3_3 17 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 177 205 (accept_3_3 14 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 177 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 177 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 177 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 205 (accept_3_3 11 177 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 205
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 177 205 (accept_3_3 8 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  177 205 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 177 205 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 177 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 205 (accept_3_3 5 177 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 3 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 205 (accept_3_3 2 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 177 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 205))))))))))))))))))))))))))))) (allB_succ' 30 176 205 (Eq.refl Bool.true) (allA_of_3_1 30
  176 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 175 205 (Eq.refl Bool.true) (allA_succ_of_gcd 30 175
  205 5 6 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  175 205 (accept_3_3 29 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 205
  (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 175 205 (Polychromatic418967fa.accept_19_8_4_15_1_1414 27 175 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 205 (accept_3_3 26 175 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 175 205 5 5 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 175 205 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 205 (accept_3_3 23 175 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 205
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 175 205 5 4 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 175 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 205 (accept_3_3 17 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 205
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 175 205 5 3 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 175 205 (accept_3_3 14 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 205 (Polychromatic418967fa.accept_19_13_4_15_1_7902 13 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 205 (accept_3_3 11 175 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 175 205 5 2 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 175 205 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 205 (accept_3_3 8 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 205 (Polychromatic418967fa.accept_20_7_15_5_1_6087
  7 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 175 205 5 1 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 175 205 (Polychromatic418967fa.accept_13_4_6_10_1_1199 4 175 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 205 (accept_3_3 2 175 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 1
  175 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 205)))))))))))))))))))))))))))))))
  (allB_succ' 32 174 205 (Eq.refl Bool.true) (allA_succ_of_accept 31 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50
  31 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 205
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 174 205 (accept_3_3 29 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 174 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 205 (accept_3_3 26 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 174 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 174 205 (accept_3_3 23 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 174 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 174 205 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 174 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 205 (accept_3_3 20 174 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 205
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 205 (accept_3_3 17 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 205 (accept_3_3 14 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 205
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 174 205 (accept_3_3 11 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 174 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 205 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 174 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 205 (accept_3_3 8 174 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7
  174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 205 (accept_3_3 5 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 174 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 205 (accept_3_3 2 174 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 205)))))))))))))))))))))))))))))))) (allB_succ' 33
  173 205 (Eq.refl Bool.true) (allA_of_3_1 33 173 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 172 205
  (Eq.refl Bool.true) (allA_succ_of_accept 33 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 205 (accept_3_3 32 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 172 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 172 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 172 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 172 205 (accept_3_3 29 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 172 205 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 172 205 (accept_3_3 26 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 172 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 172 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 172 205 (accept_3_3 23 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 172 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 205 (accept_3_3 20 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 172 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 205
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 172 205 (accept_3_3 17 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 172 205 (Polychromatic418967fa.accept_14_2_4_9_1_2121 16 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 205 (accept_3_3 14 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 172 205 (accept_3_3 11 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 172 205 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 205 (accept_3_3 8 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 205 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 172 205 (accept_3_3 5 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  172 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 172 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 172 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 205 (accept_3_3 2 172 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 172 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 205)))))))))))))))))))))))))))))))))) (allB_succ' 35
  171 205 (Eq.refl Bool.true) (allA_succ_of_accept 34 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 171 205 (accept_3_3 32 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 171 205 (Polychromatic418967fa.accept_13_5_2_10_1_248 31 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 205 (accept_3_3 29 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 205
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 171 205 (accept_3_3 26 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 171 205 (Polychromatic418967fa.accept_13_12_2_10_1_2698 25 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 171 205 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 205 (accept_3_3 23 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 171 205 (accept_3_3 20 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 171 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 205 (accept_3_3 17 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 205
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 205 (accept_3_3 14 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 205 (accept_3_3 11 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 205
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 205 (accept_3_3 8 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 205 (Polychromatic418967fa.accept_21_7_3_16_1_7337 7 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 205 (accept_3_3 5 171 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 205
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 205 (accept_3_3 2 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 171 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 205))))))))))))))))))))))))))))))))))) (allB_succ' 36 170 205 (Eq.refl Bool.true)
  (allA_of_3_1 36 170 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 169 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 169 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 36 169 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 205 (accept_3_3 35 169 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 169 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 169 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 205
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 205 (accept_3_3 32 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 205 (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 205 (accept_3_3 29 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 169 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 205 (accept_3_3 26 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 205 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 169 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 205 (accept_3_3 23 169 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 205 (Polychromatic418967fa.accept_14_8_1_9_1_2085 22 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 205
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 205 (accept_3_3 20 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 205 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 205 (Polychromatic418967fa.accept_27_18_7_16_1_8156 18 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 205 (accept_3_3 17 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 205 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 169
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 205
  (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 169 205 (accept_3_3 14 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 169 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 169 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 169 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 205 (accept_3_3 11 169 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 205 (Polychromatic418967fa.accept_7_3_1_2_1_247
  10 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 205
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 205 (accept_3_3 8 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 205 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 205 (accept_3_3 5 169 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 4 169 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 205
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 205 (accept_3_3 2 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 205 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 169 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 205))))))))))))))))))))))))))))))))))))) (allB_succ' 38 168 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 168 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 205 (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 168
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 205 (accept_3_3 35 168
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 205
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 168 205 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 168 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 205 (accept_3_3 32 168 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 168 205 (accept_3_3 29 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 168 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 168 205 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 168 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 168 205 (accept_3_3 26 168 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 205 (Polychromatic418967fa.accept_19_6_16_15_1_9250 25 168
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 205
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 168 205 (accept_3_3 23 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 168 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 168 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 168 205 (accept_3_3 20 168 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 205 (Polychromatic418967fa.accept_9_1_6_7_1_285
  19 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 205
  (Polychromatic418967fa.accept_19_18_16_15_1_5044 18 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 168 205 (accept_3_3 17 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 205 (Polychromatic418967fa.accept_17_16_15_1_1_11968 16 168 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 205 (Polychromatic418967fa.accept_11_4_3_7_1_828
  15 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 168 205 (accept_3_3 14
  168 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 205
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 168 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 205 (accept_3_3 11 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 168 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 168 205 (Polychromatic418967fa.accept_13_9_12_10_1_242
  9 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 205 (accept_3_3 8
  168 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 205
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 168 205 (Polychromatic418967fa.accept_13_6_12_10_1_690 6 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 205 (accept_3_3 5 168 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 168 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 168 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 3
  168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 168 205 (accept_3_3 2 168
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 205
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 205)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 167 205 (Eq.refl Bool.true) (allA_of_3_1 39 167
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 40 166 205 (Eq.refl Bool.true) (allA_succ_of_accept 39 166
  205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 166 205 (accept_3_3 38 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 166 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 166 205 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 166 205 (accept_3_3 35 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 166 205 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 166 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 166 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 166 205 (accept_3_3 32 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 166 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 166 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 166 205 (accept_3_3 29 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 166 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 166 205 (accept_3_3 26 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 166 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 166 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 205 (accept_3_3 23 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 205 (Polychromatic418967fa.accept_15_7_1_10_1_305 22 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 166 205 (accept_3_3 20 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 166 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 166 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 205 (accept_3_3 17 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 166 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 166 205 (accept_3_3 14 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 166 205 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 166 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 205 (accept_3_3 11 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 166 205 (accept_3_3 8 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  166 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 166 205 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 205 (accept_3_3 5 166 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 166 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 166 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 166 205 (accept_3_3 2 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  166 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 166 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 166 205)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 165 205 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 165 205 5 8 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 165 205 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 205 (accept_3_3 38 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 165 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 165 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 205
  (Polychromatic418967fa.accept_19_17_13_15_1_1402 36 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 165 205 5 7 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 165 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 165 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 205 (accept_3_3 32 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 165 205 5 6 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 165 205 (accept_3_3 29 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 165 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 205 (accept_3_3 26 165 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 205 5 5 33 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 165 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 205 (accept_3_3 23 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 205 (Polychromatic418967fa.accept_19_2_13_15_1_9274 21 165 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 205 5 4 33 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 165 205 (Polychromatic418967fa.accept_16_2_5_13_1_3842 18 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 205 (accept_3_3 17 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 205 5 3 33 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 205 (accept_3_3 14 165 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 165 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 205 (accept_3_3 11 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  165 205 5 2 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 165 205 (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 205 (accept_3_3 8 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 205 (Polychromatic418967fa.accept_19_7_13_15_1_2407 7 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 205 5 1 33 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 205
  (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 165 205 (Polychromatic418967fa.accept_12_3_9_1_1_290 3 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 205 (accept_3_3 2 165 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 165 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 165 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 205))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 164
  205 (Eq.refl Bool.true) (allA_of_3_1 42 164 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 163 205
  (Eq.refl Bool.true) (allA_succ_of_accept 42 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 205 (accept_3_3 41 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 163 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 205 (accept_3_3 38 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 205 (Polychromatic418967fa.accept_22_14_9_7_1_11988 36 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 205 (accept_3_3 35 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 205 (accept_3_3 32 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 205 (accept_3_3 29 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 205 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 205
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 205 (accept_3_3 26 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 205 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 205 (Polychromatic418967fa.accept_9_6_1_7_1_577 24 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 205 (accept_3_3 23 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 205 (accept_3_3 20 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 205 (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 205 (accept_3_3 17 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 205 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 205 (accept_3_3 14 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 205 (accept_3_3 11 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 205
  (Polychromatic418967fa.accept_17_9_10_1_1_3345 9 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 205 (accept_3_3 8 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 205 (accept_3_3 5 163 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 205 (accept_3_3 2 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 205 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 163 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 205))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 162 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 205 (Polychromatic418967fa.accept_13_3_6_10_1_2658 42 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 162 205 (accept_3_3 41 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 205
  (Polychromatic418967fa.accept_22_18_8_7_1_11987 40 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 205 (accept_3_3 38 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 205 (Polychromatic418967fa.accept_10_7_2_5_1_298 37 162 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 205
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 205 (accept_3_3 35 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 162 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 205 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 205 (accept_3_3 32 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 162 205 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 162 205 (accept_3_3 29 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 162 205 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 162 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 162 205 (accept_3_3 26 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 162 205 (Polychromatic418967fa.accept_13_12_6_10_1_667 25 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 162 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 205 (accept_3_3 23 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 205 (Polychromatic418967fa.accept_13_9_6_10_1_666 22 162 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 205
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 21 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 162 205 (accept_3_3 20 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 205 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 162 205 (accept_3_3 17 162
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 205
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 205 (accept_3_3 14 162 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 162 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 205
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 205 (accept_3_3 11 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 205 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 205 (accept_3_3 8 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 205 (accept_3_3 5 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 205 (Polychromatic418967fa.accept_11_4_8_7_1_819 4 162 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 205 (accept_3_3 2 162 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 205 (Polychromatic418967fa.accept_14_1_8_9_1_1312 1 162 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 205))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 161 205 (Eq.refl Bool.true) (allA_of_3_1 45 161 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 160 205 (Eq.refl Bool.true) (allA_succ_of_gcd 45 160 205 5 9 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 160 205 (accept_3_3 44 160 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 205
  (Polychromatic418967fa.accept_17_8_7_1_1_4521 42 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 205 (accept_3_3 41 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  160 205 5 8 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 160 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 160 205 (accept_3_3 38 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 160 205 (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 160 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 36
  160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 160 205 5 7 32 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 160 205
  (Polychromatic418967fa.accept_11_1_6_7_1_116 34 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 160 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 205 (accept_3_3 32 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 160 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 160 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 205 5 6 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 205 (accept_3_3 29 160 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 205 (Polychromatic418967fa.accept_17_11_7_1_1_7023 28 160
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 160 205 (accept_3_3 26 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  160 205 5 5 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 160 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 160 205 (accept_3_3 23 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 160 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 160 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 205 5 4 32 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 205
  (Polychromatic418967fa.accept_13_6_4_10_1_660 19 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 160 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 205 (accept_3_3 17 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 160 205 (Polychromatic418967fa.accept_19_16_8_15_1_6447 16 160 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 160 205 5 3 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 160 205 (accept_3_3 14 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 205
  (Polychromatic418967fa.accept_22_13_6_7_1_11986 13 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 160 205 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 160 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 205 (accept_3_3 11 160 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 205 5 2 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 205 (accept_3_3 8 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 205 (Polychromatic418967fa.accept_13_7_4_10_1_2675
  7 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 205
  (Polychromatic418967fa.accept_13_6_4_10_1_660 6 160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 160 205 5 1 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 160 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 160 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 205 (accept_3_3 2 160 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  160 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  205)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 159 205 (Eq.refl Bool.true) (allA_succ_of_accept 46
  159 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 205 (accept_3_3 44 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 205 (Polychromatic418967fa.accept_25_18_9_5_1_11985 43 159 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 205 (accept_3_3 41 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 205 (accept_3_3 38 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 205
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 205 (accept_3_3 35 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 205 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 205 (accept_3_3 32 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 159 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 205 (accept_3_3 29 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 205 (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 205 (accept_3_3 26 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 159 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 205
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 205 (accept_3_3 23 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 205 (accept_3_3 20 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 205 (accept_3_3 17 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 205 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 205 (accept_3_3 14 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 159 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 205 (accept_3_3 11 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 205 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 205 (accept_3_3 8 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 205 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 205 (accept_3_3 5 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 205 (accept_3_3 2 159 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 159 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 205)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 158 205 (Eq.refl Bool.true) (allA_of_3_1 48 158 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 157 205 (Eq.refl Bool.true) (allA_succ_of_accept 48 157 205 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 205 (accept_3_3 47
  157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 205
  (Polychromatic418967fa.accept_9_1_4_7_1_7 46 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 157 205 (Polychromatic418967fa.accept_21_3_10_16_1_4340 45 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 205 (accept_3_3 44 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 205 (accept_3_3 41 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 205 (accept_3_3 38 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 205
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 205 (accept_3_3 35 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 205 (accept_3_3 32 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 205
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 205 (accept_3_3 29 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 205 (accept_3_3 26 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 205 (Polychromatic418967fa.accept_17_8_4_1_1_5730 25 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 205 (accept_3_3 23 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 205 (accept_3_3 20 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 205
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 205 (accept_3_3 17 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 205 (accept_3_3 14 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 205 (accept_3_3 11 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 205 (Polychromatic418967fa.accept_13_9_1_10_1_647 9 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 205 (accept_3_3 8 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 205 (Polychromatic418967fa.accept_21_7_10_16_1_4338 7 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 205
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 205 (accept_3_3 5 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 205 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 157 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 205 (accept_3_3 2 157 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 205)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 156 205 (Eq.refl Bool.true) (allA_succ_of_accept 49 156 205 (Polychromatic418967fa.accept_8_1_4_5_1_48
  49 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 205
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 48 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 156 205 (accept_3_3 47 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 156 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 156 205 (Polychromatic418967fa.accept_21_3_9_16_1_10597 45 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 205 (accept_3_3 44 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 205 (Polychromatic418967fa.accept_17_9_3_1_1_2275 43 156
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 205 (accept_3_3 41 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 205 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 205 (accept_3_3 38 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 205
  (Polychromatic418967fa.accept_16_4_12_13_1_990 36 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 205 (accept_3_3 35 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 205 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 156 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 205 (accept_3_3 32 156 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 205
  (Polychromatic418967fa.accept_19_11_4_15_1_5052 30 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 205 (accept_3_3 29 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 156 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 205 (Polychromatic418967fa.accept_15_12_6_10_1_1516 27 156
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 205 (accept_3_3 26 156
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 205
  (Polychromatic418967fa.accept_8_1_4_5_1_48 25 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 156 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 156 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 205 (accept_3_3 23 156 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 156 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 156 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 205 (Polychromatic418967fa.accept_10_1_6_5_1_304
  21 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 205 (accept_3_3 20
  156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 205
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 156 205 (Polychromatic418967fa.accept_14_4_2_9_1_2092 18 156 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 205 (accept_3_3 17 156 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 156 205 (Polychromatic418967fa.accept_15_1_6_10_1_23 16 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 156 205 (accept_3_3 14 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 156 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 156 205 (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 205 (accept_3_3 11 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 156 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 205
  (Polychromatic418967fa.accept_8_1_4_5_1_48 9 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 156 205 (accept_3_3 8 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  156 205 (Polychromatic418967fa.accept_14_7_2_9_1_2093 7 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 156 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 156 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 205 (accept_3_3 5 156 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 156 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 205
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 156 205 (accept_3_3 2 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  156 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 156 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 205)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 155 205 (Eq.refl
  Bool.true) (allA_of_3_1 51 155 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 154 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 205 (accept_3_3 50 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 154 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 154 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 48
  154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 205 (accept_3_3 47
  154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 205
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 154 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 205 (accept_3_3 44 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 154 205 (Polychromatic418967fa.accept_9_6_1_7_1_577
  42 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 154 205 (accept_3_3 41
  154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 205
  (Polychromatic418967fa.accept_9_4_1_7_1_293 40 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 205 (accept_3_3 38 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 154 205 (Polychromatic418967fa.accept_15_7_4_10_1_1513 37 154 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 205
  (Polychromatic418967fa.accept_10_6_4_5_1_615 36 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 154 205 (accept_3_3 35 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 154 205 (Polychromatic418967fa.accept_13_8_11_10_1_636 34 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 154 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 205 (accept_3_3 32 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 205 (accept_3_3 29 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 154 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 205 (accept_3_3 26 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 205 (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 154 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 205 (accept_3_3 23 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 205 (accept_3_3 20 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 205
  (Polychromatic418967fa.accept_19_18_2_15_1_3718 18 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 154 205 (accept_3_3 17 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 154 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 154 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 205 (accept_3_3 14 154 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 205 (Polychromatic418967fa.accept_9_4_1_7_1_293
  13 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 205 (accept_3_3 11 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 205 (Polychromatic418967fa.accept_20_10_14_5_1_3331 10 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 205 (accept_3_3 8 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 154 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 205 (accept_3_3 5 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 154 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 205 (accept_3_3 2 154 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 205 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 154 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  205)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 153 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 205 (Polychromatic418967fa.accept_12_3_9_1_1_290 51 153
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 205 (accept_3_3 50 153
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 205
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 49 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 153 205 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 205 (accept_3_3 47 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 45
  153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 205 (accept_3_3 44
  153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 205
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 153 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 205 (accept_3_3 41 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 205 (Polychromatic418967fa.accept_7_4_6_2_1_451
  39 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 205 (accept_3_3 38
  153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 205
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 205 (accept_3_3 35 153 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 205
  (Polychromatic418967fa.accept_16_1_9_13_1_1822 33 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 205 (accept_3_3 32 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 205 (Polychromatic418967fa.accept_19_11_1_15_1_9263 30 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 205 (accept_3_3 29 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 205
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 205 (accept_3_3 26 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 205 (accept_3_3 23 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 205
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 21 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 205 (accept_3_3 20 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 205 (Polychromatic418967fa.accept_20_19_13_5_1_7722 19 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 205 (accept_3_3 17 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 205
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 205 (accept_3_3 14 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 205 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 12 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 205 (accept_3_3 11 153 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 205
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 205 (accept_3_3 8 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 205 (Polychromatic418967fa.accept_15_6_3_10_1_2341 6 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 205 (accept_3_3 5 153 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 205 (accept_3_3 2 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 205))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 152 205 (Eq.refl
  Bool.true) (allA_of_3_1 54 152 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 151 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 151 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 205 (accept_3_3 53 151 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 151 205 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 205
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 51 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 151 205 (accept_3_3 50 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 151 205 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 151 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 205 (accept_3_3 47 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46
  151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 205
  (Polychromatic418967fa.accept_19_7_18_15_1_5061 45 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 151 205 (accept_3_3 44 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 151 205 (Polychromatic418967fa.accept_13_4_8_10_1_671 43 151 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 205 (accept_3_3 41 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 205 (Polychromatic418967fa.accept_7_5_4_2_1_235
  40 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 205
  (Polychromatic418967fa.accept_10_9_1_5_1_594 39 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 205 (accept_3_3 38 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 205 (Polychromatic418967fa.accept_11_4_8_7_1_819 37 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 205 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 205 (accept_3_3 35 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 205 (accept_3_3 32 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 205 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 205 (accept_3_3 29 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 205 (Polychromatic418967fa.accept_13_2_8_10_1_1902 28 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 205 (accept_3_3 26 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 205 (Polychromatic418967fa.accept_13_12_8_10_1_1879 25 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 205 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 205 (accept_3_3 23 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 205
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 21 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 205 (accept_3_3 20 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 205 (accept_3_3 17 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 205 (Polychromatic418967fa.accept_10_6_1_5_1_1024 16 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 205
  (Polychromatic418967fa.accept_11_4_8_7_1_819 15 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 205 (accept_3_3 14 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 205 (accept_3_3 11 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 205
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 205 (accept_3_3 8 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 205 (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 205 (accept_3_3 5 151 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 205 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 151 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 205
  (Polychromatic418967fa.accept_17_3_15_1_1_3348 3 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 205 (accept_3_3 2 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 205 (Polychromatic418967fa.accept_24_1_7_13_1_11961 1 151 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 205))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 150 205 (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 150 205 5 11 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 150 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 150 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 150 205 (accept_3_3 53 150 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 205 (Polychromatic418967fa.accept_16_4_6_13_1_1874 52 150
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 205 5 10 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 49 150 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 205 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 205 (accept_3_3 47
  150 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 150 205
  (Polychromatic418967fa.accept_9_1_6_7_1_285 46 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 150 205 5 9 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 150 205 (accept_3_3 44 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 150 205 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 150 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 205 (accept_3_3 41 150 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 205 5 8 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 205 (accept_3_3 38
  150 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 205
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 150 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 150 205 5 7 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 150 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 34
  150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 150 205 (accept_3_3 32 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 205 5 6 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 205 (accept_3_3 29 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 150 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 205 (accept_3_3 26 150 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 150 205 5 5 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 150 205
  (Polychromatic418967fa.accept_19_5_17_15_1_9225 24 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 205 (accept_3_3 23 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 205 5 4 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 150 205 (Polychromatic418967fa.accept_20_18_10_5_1_3306 18 150 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 150 205 (accept_3_3 17 150 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 205 (Polychromatic418967fa.accept_13_3_7_10_1_668 16 150 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 205 5 3 30 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 205 (accept_3_3 14 150 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 205 (Polychromatic418967fa.accept_7_6_3_2_1_461
  13 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 205 (accept_3_3 11 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  150 205 5 2 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 150 205 (Polychromatic418967fa.accept_16_9_6_13_1_3831 9 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 150 205 (accept_3_3 8 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 150 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 150 205 5 1 30 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 150 205
  (Polychromatic418967fa.accept_9_4_6_7_1_286 4 150 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 150 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 205 (accept_3_3 2 150 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 150 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 149 205 (Eq.refl Bool.true) (allA_of_3_1 57 149 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 58 148 205 (Eq.refl Bool.true) (allA_succ_of_accept 57 148 205 (Polychromatic418967fa.accept_6_3_4_1_1_8
  57 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 205 (accept_3_3 56
  148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 148 205 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 148 205 (accept_3_3 53 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 148 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 148 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 51
  148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 205 (accept_3_3 50
  148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 205
  (Polychromatic418967fa.accept_8_1_4_5_1_48 49 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 148 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 148 205 (accept_3_3 47 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 148 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 45
  148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 205 (accept_3_3 44
  148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 205
  (Polychromatic418967fa.accept_10_3_8_5_1_606 43 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 148 205 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 205 (accept_3_3 41 148 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 148 205 (Polychromatic418967fa.accept_16_8_4_13_1_1014 40 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 148 205 (accept_3_3 38 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 148 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 148 205 (Polychromatic418967fa.accept_21_15_1_16_1_2930 36 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 205 (accept_3_3 35 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 148 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 148 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 148 205 (accept_3_3 32 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 148 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 148 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 205 (accept_3_3 29 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 148 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 148 205 (accept_3_3 26 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 148 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 25 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 148 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 205 (accept_3_3 23 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 205 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 205 (accept_3_3 20 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 205 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 205 (accept_3_3 17 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 205 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 148
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 205 (accept_3_3 14 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 205 (accept_3_3 11 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 205 (accept_3_3 8 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 205 (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 205 (accept_3_3 5 148 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 205 (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 148 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 205 (accept_3_3 2 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 1 148 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 147 205
  (Eq.refl Bool.true) (allA_succ_of_accept 58 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 205 (accept_3_3 56 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 55 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 205 (accept_3_3 53 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 205 (accept_3_3 50 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 205 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 205 (accept_3_3 47 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 205 (accept_3_3 44 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 205 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 205 (accept_3_3 41 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 205
  (Polychromatic418967fa.accept_15_9_12_10_1_809 39 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 205 (accept_3_3 38 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 205 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 205 (accept_3_3 35 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 205 (accept_3_3 32 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 205 (accept_3_3 29 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 205
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 205 (accept_3_3 26 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 205 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 205 (accept_3_3 23 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 205 (accept_3_3 20 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 19 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 205 (accept_3_3 17 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 205 (accept_3_3 14 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 205 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 205 (accept_3_3 11 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 205 (accept_3_3 8 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 205 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 205 (accept_3_3 5 147 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 205
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 205 (accept_3_3 2 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 147 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 146 205
  (Eq.refl Bool.true) (allA_of_3_1 60 146 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 145 205 (Eq.refl
  Bool.true) (allA_succ_of_gcd 60 145 205 5 12 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 145 205 (accept_3_3 59 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 145 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 205 (accept_3_3 56 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 145 205 5 11 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 145 205
  (Polychromatic418967fa.accept_17_3_9_1_1_1344 54 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 205 (accept_3_3 53 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 205 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 145 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 145 205 5 10 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 145 205
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 145 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 48 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 205 (accept_3_3 47 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 145 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 145 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 145 205 5 9 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 145 205 (accept_3_3 44 145 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 205 (Polychromatic418967fa.accept_19_5_12_15_1_9244 43 145
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 205 (accept_3_3 41 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  145 205 5 8 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 145 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 145 205 (accept_3_3 38 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 145 205 (Polychromatic418967fa.accept_13_11_2_10_1_4399 37 145 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 205 (Polychromatic418967fa.accept_8_4_1_5_1_186
  36 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 205 5 7 29 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 205
  (Polychromatic418967fa.accept_13_8_2_10_1_652 34 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 205 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 205 (accept_3_3 32 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 145 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 205 5 6 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 205 (accept_3_3 29 145 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 28 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 205
  (Polychromatic418967fa.accept_17_10_9_1_1_7062 27 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 205 (accept_3_3 26 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  145 205 5 5 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 145 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 205 (accept_3_3 23 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 205 5 4 29 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 205
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 19 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 145 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 205 (accept_3_3 17 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 205 (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 145 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 205 5 3 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 205 (accept_3_3 14 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 205 (Polychromatic418967fa.accept_9_4_1_7_1_293
  13 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 205
  (Polychromatic418967fa.accept_8_4_1_5_1_186 12 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 205 (accept_3_3 11 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 205 5 2 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 205 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 205 (accept_3_3 8 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 205 (Polychromatic418967fa.accept_14_7_5_9_1_2911 7 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 205 (Polychromatic418967fa.accept_9_6_1_7_1_577 6 145 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 205 5 1 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 205
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 205 (accept_3_3 2 145 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 205 (Polychromatic418967fa.accept_21_1_19_16_1_2901 1 145 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 144 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 144 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 205 (Polychromatic418967fa.accept_17_9_8_1_1_7036 60 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 144 205 (accept_3_3 59 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 205
  (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 144 205 (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 205 (accept_3_3 56 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 144 205 (accept_3_3 53 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 144 205 (Polychromatic418967fa.accept_19_14_11_15_1_9230 52 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 205 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 205 (accept_3_3 50 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 205 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 144 205 (accept_3_3 47 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 144 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 46 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 205 (Polychromatic418967fa.accept_17_11_8_1_1_3362 45 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 205 (accept_3_3 44 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 205 (Polychromatic418967fa.accept_13_4_1_10_1_693 43 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 205
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 42 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 144 205 (accept_3_3 41 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 144 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 205 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 205 (accept_3_3 38 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 205
  (Polychromatic418967fa.accept_13_11_1_10_1_648 37 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 144 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 144 205 (accept_3_3 35 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 144 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 205 (Polychromatic418967fa.accept_7_5_4_2_1_235
  33 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 205 (accept_3_3 32
  144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 205
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 31 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 144 205 (Polychromatic418967fa.accept_13_4_1_10_1_693 30 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 144 205 (accept_3_3 29 144 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 144 205 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 205
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 144 205 (accept_3_3 26 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 144 205 (Polychromatic418967fa.accept_19_6_11_15_1_2527 25 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 144 205 (Polychromatic418967fa.accept_13_11_1_10_1_648 24 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 144 205 (accept_3_3 23 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 205 (Polychromatic418967fa.accept_13_9_1_10_1_647 22 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 205
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 144 205 (accept_3_3 20 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 144 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 144 205 (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 144 205 (accept_3_3 17 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 205 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 144
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 205
  (Polychromatic418967fa.accept_20_15_4_5_1_7759 15 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 144 205 (accept_3_3 14 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 144 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 144 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 144 205 (accept_3_3 11 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 205 (Polychromatic418967fa.accept_19_10_11_15_1_3699 10 144 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 205
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 144 205 (accept_3_3 8 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  144 205 (Polychromatic418967fa.accept_17_7_8_1_1_1373 7 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 144 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 144 205 (accept_3_3 5 144 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 205 (Polychromatic418967fa.accept_13_4_1_10_1_693 4 144 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 205
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 144 205 (accept_3_3 2 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  144 205 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 144 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 143 205
  (Eq.refl Bool.true) (allA_of_3_1 63 143 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 142 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 205 (accept_3_3 62 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 205 (Polychromatic418967fa.accept_13_9_12_10_1_242 61 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 205
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 142 205 (accept_3_3 59 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 142 205 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 142 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 142 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 205 (accept_3_3 56 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 205
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 54 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 142 205 (accept_3_3 53 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 142 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 142 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 205 (accept_3_3 50 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 205 (Polychromatic418967fa.accept_14_7_2_9_1_2093
  49 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 205
  (Polychromatic418967fa.accept_10_8_2_5_1_596 48 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 205 (accept_3_3 47 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 205 (Polychromatic418967fa.accept_13_7_12_10_1_640 46 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 205 (accept_3_3 44 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 205
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 142 205 (accept_3_3 41 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 142 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 142 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 205 (accept_3_3 38 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 205 (Polychromatic418967fa.accept_10_7_2_5_1_298
  37 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 205
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 205 (accept_3_3 35 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 205 (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 205 (accept_3_3 32 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 142 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 205
  (Polychromatic418967fa.accept_19_11_9_15_1_5055 30 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 142 205 (accept_3_3 29 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 142 205 (Polychromatic418967fa.accept_10_8_2_5_1_596 28 142 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 205 (accept_3_3 26 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 205 (Polychromatic418967fa.accept_11_3_10_7_1_129
  25 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 205
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 24 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 142 205 (accept_3_3 23 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 142 205 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 142 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 205 (accept_3_3 20 142 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19
  142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 205
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 205 (accept_3_3 17 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 205 (accept_3_3 14 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 205 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 142 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 205
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 142 205 (accept_3_3 11 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 142 205 (Polychromatic418967fa.accept_16_10_14_13_1_1870 10 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9
  142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 205 (accept_3_3 8 142
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50
  7 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 205
  (Polychromatic418967fa.accept_13_6_12_10_1_690 6 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 205 (accept_3_3 5 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 142 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 205 (accept_3_3 2 142 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 142 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 141 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 205 (Polychromatic418967fa.accept_12_3_9_1_1_290 63 141
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 205 (accept_3_3 62 141
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 205
  (Polychromatic418967fa.accept_15_1_6_10_1_23 61 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 141 205 (Polychromatic418967fa.accept_11_5_9_7_1_411 60 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 205 (accept_3_3 59 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 205 (Polychromatic418967fa.accept_9_3_6_7_1_562
  57 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 205 (accept_3_3 56
  141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 141 205 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 205 (accept_3_3 53 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 205 (Polychromatic418967fa.accept_12_3_9_1_1_290
  51 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 205 (accept_3_3 50
  141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 205
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 141 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 205 (accept_3_3 47 141 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 205 (Polychromatic418967fa.accept_7_3_1_2_1_247
  45 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 205 (accept_3_3 44
  141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 205
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 43 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 205 (Polychromatic418967fa.accept_13_3_11_10_1_2647 42 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 205 (accept_3_3 41 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 39 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 205 (accept_3_3 38 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 205 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 205 (accept_3_3 35 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 205
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 205 (accept_3_3 32 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 30 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 205 (accept_3_3 29 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 205 (accept_3_3 26 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 205 (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 205 (accept_3_3 23 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 205 (accept_3_3 20 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 205 (Polychromatic418967fa.accept_15_3_6_10_1_1539 18 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 205 (accept_3_3 17 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 205 (accept_3_3 14 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 12 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 205 (accept_3_3 11 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 205
  (Polychromatic418967fa.accept_10_9_1_5_1_594 9 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 205 (accept_3_3 8 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 205 (Polychromatic418967fa.accept_19_7_8_15_1_2448 7 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 205 (accept_3_3 5 141 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 205
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 205 (accept_3_3 2 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 141 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 140 205
  (Eq.refl Bool.true) (allA_of_3_1 66 140 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 139 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 205 (accept_3_3 65 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 205
  (Polychromatic418967fa.accept_25_13_14_5_1_11984 63 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 139 205 (accept_3_3 62 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 139 205 (Polychromatic418967fa.accept_10_1_9_5_1_83 61 139 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 139 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 205 (accept_3_3 59 139 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 205
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 205 (accept_3_3 56 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 205 (accept_3_3 53 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 51 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 205 (accept_3_3 50 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 205 (Polychromatic418967fa.accept_17_15_3_1_1_9696 49 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 205 (accept_3_3 47 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 205 (accept_3_3 44 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 205 (accept_3_3 41 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 205 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 205
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 205 (accept_3_3 38 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 205 (accept_3_3 35 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 33 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 205 (accept_3_3 32 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 205 (accept_3_3 29 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 205
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 205 (accept_3_3 26 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 205 (accept_3_3 23 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 205
  (Polychromatic418967fa.accept_9_3_4_7_1_89 21 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 205 (accept_3_3 20 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 205 (accept_3_3 17 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 205 (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 205
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 205 (accept_3_3 14 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 205 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 205 (accept_3_3 11 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 205
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 205 (accept_3_3 8 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 205 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 205 (accept_3_3 5 139 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 205 (accept_3_3 2 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 139 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 138
  205 (Eq.refl Bool.true) (allA_succ_of_accept 67 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 205
  (Polychromatic418967fa.accept_7_3_5_2_1_17 66 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 138 205 (accept_3_3 65 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 138 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 64 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 205 (accept_3_3 62 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 205 (Polychromatic418967fa.accept_19_4_5_15_1_2437 61 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 205
  (Polychromatic418967fa.accept_7_4_5_2_1_243 60 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 205 (accept_3_3 59 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 205 (Polychromatic418967fa.accept_10_7_8_5_1_1008 57 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 205 (accept_3_3 56 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 205
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 54 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 205 (accept_3_3 53 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 205 (accept_3_3 50 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 205
  (Polychromatic418967fa.accept_19_10_5_15_1_6443 48 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 205 (accept_3_3 47 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 138 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 205 (accept_3_3 44 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43
  138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 138 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 138 205 (accept_3_3 41 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 138 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 205 (accept_3_3 38 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 138 205
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 138 205 (accept_3_3 35 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 138 205 (Polychromatic418967fa.accept_11_1_6_7_1_116 34 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 138 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 205 (accept_3_3 32 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 138 205
  (Polychromatic418967fa.accept_13_4_8_10_1_671 30 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 138 205 (accept_3_3 29 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 138 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 205 (accept_3_3 26 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 138 205
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 138 205 (accept_3_3 23 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 138 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 138 205 (Polychromatic418967fa.accept_14_7_12_9_1_2926 21 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 205 (accept_3_3 20 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 138 205
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 138 205 (accept_3_3 17 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 138 205 (Polychromatic418967fa.accept_17_16_2_1_1_4492 16 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 205 (accept_3_3 14 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 13 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 138 205
  (Polychromatic418967fa.accept_10_2_8_5_1_587 12 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 138 205 (accept_3_3 11 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 138 205 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 138 205 (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 205 (accept_3_3 8 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 138 205
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 138 205 (accept_3_3 5 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  138 205 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 138 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 138 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 205 (accept_3_3 2 138 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 138 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 137 205 (Eq.refl Bool.true)
  (allA_of_3_1 69 137 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 136 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 136 205 (accept_3_3 68 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 136 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 136 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 66
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 136 205 (accept_3_3 65
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 136 205
  (Polychromatic418967fa.accept_7_1_3_2_1_13 64 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 136 205 (accept_3_3 62 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 136 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 136 205 (Polychromatic418967fa.accept_9_6_1_7_1_577
  60 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 136 205 (accept_3_3 59
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 136 205
  (Polychromatic418967fa.accept_9_4_1_7_1_293 58 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 205 (accept_3_3 56 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 136 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 205 (Polychromatic418967fa.accept_7_5_3_2_1_249
  54 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 205 (accept_3_3 53
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 205
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 52 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 205 (accept_3_3 50 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 136 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 205 (Polychromatic418967fa.accept_7_6_3_2_1_461
  48 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 205 (accept_3_3 47
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 205
  (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 205 (accept_3_3 44 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 136 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 205 (Polychromatic418967fa.accept_9_6_1_7_1_577
  42 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 205 (accept_3_3 41
  136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 40 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 205 (accept_3_3 38 136 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 136 205 (Polychromatic418967fa.accept_15_7_1_10_1_305 37 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 205
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 205 (accept_3_3 35 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 205 (accept_3_3 32 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 205 (accept_3_3 29 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 205 (Polychromatic418967fa.accept_13_2_6_10_1_2703 28 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 205 (accept_3_3 26 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 205 (Polychromatic418967fa.accept_11_3_4_7_1_114 25 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 205 (accept_3_3 23 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 205 (accept_3_3 20 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 205
  (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 205 (accept_3_3 17 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 205 (Polychromatic418967fa.accept_13_3_6_10_1_2658 16 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 205 (accept_3_3 14 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 205 (accept_3_3 11 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 205 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 205 (accept_3_3 8 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 205 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 205
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 205 (accept_3_3 5 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 136 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 205 (accept_3_3 2 136 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 136 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 135 205 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 135 205 5 14 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 135 205 (Polychromatic418967fa.accept_12_9_3_1_1_303 69 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 205 (accept_3_3 68 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 205 (Polychromatic418967fa.accept_13_2_5_10_1_250 67 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 135 205 5 13 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 135 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 205
  (Polychromatic418967fa.accept_17_12_16_1_1_8363 63 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 205 (accept_3_3 62 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 205 (Polychromatic418967fa.accept_20_1_15_5_1_9135 61 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 205 5 12 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 205 (accept_3_3 59 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 205
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 205 (accept_3_3 56 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  135 205 5 11 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 205 (accept_3_3 53 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 205
  (Polychromatic418967fa.accept_19_13_2_15_1_7920 51 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 135 205 5 10 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 135 205 (Polychromatic418967fa.accept_17_15_16_1_1_7080 49 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 205
  (Polychromatic418967fa.accept_11_4_3_7_1_828 48 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 135 205 (accept_3_3 47 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 135 205 5 9 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 135 205 (accept_3_3 44 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 205 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 205 (accept_3_3 41 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 205 5 8 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 135 205
  (Polychromatic418967fa.accept_17_5_16_1_1_3358 39 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 205 (accept_3_3 38 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 205 (Polychromatic418967fa.accept_11_4_3_7_1_828 37 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 205 (Polychromatic418967fa.accept_16_4_7_13_1_2795 36 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 205 5 7 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 205 (Polychromatic418967fa.accept_12_9_3_1_1_303 33 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 205 (accept_3_3 32 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 205 (Polychromatic418967fa.accept_20_11_15_5_1_10632 31 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 205 5 6 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 205 (accept_3_3 29 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28
  135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 205
  (Polychromatic418967fa.accept_19_8_2_15_1_2426 27 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 205 (accept_3_3 26 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  135 205 5 5 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 135 205 (Polychromatic418967fa.accept_18_6_9_7_1_2905 24 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 205 (accept_3_3 23 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 205 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 135
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 205 5 4 27 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 205
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 205 (accept_3_3 17 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 205 5 3 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 205 (accept_3_3 14 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 205 (Polychromatic418967fa.accept_19_13_2_15_1_7920 13 135
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 205
  (Polychromatic418967fa.accept_17_12_16_1_1_8363 12 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 205 (accept_3_3 11 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 135 205 5 2 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 135 205 (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 205 (accept_3_3 8 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 135 205 (Polychromatic418967fa.accept_20_7_15_5_1_6087 7 135 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 205
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 135 205 5 1 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 135 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 205 (Polychromatic418967fa.accept_18_3_9_7_1_1839 3 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 205 (accept_3_3 2 135 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 205 (Polychromatic418967fa.accept_19_1_2_15_1_3684
  1 135 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 134 205 (Eq.refl Bool.true)
  (allA_of_3_1 72 134 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 133 205 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 133 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 72 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 133 205 (accept_3_3 71 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 133 205 (Polychromatic418967fa.accept_20_10_13_5_1_6086 70 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 205
  (Polychromatic418967fa.accept_21_6_7_16_1_9035 69 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 133 205 (accept_3_3 68 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 133 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 67 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 133 205 (Polychromatic418967fa.accept_16_2_5_13_1_3842 66 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 205 (accept_3_3 65 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 205 (Polychromatic418967fa.accept_15_4_13_10_1_1508 64 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 205
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 133 205 (accept_3_3 62 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 133 205 (Polychromatic418967fa.accept_11_6_1_7_1_1315 61 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 205 (Polychromatic418967fa.accept_22_16_1_7_1_11983 60 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 205 (accept_3_3 59 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 205
  (Polychromatic418967fa.accept_10_8_3_5_1_613 58 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 133 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 57 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 205 (accept_3_3 56 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 133 205 (Polychromatic418967fa.accept_17_4_14_1_1_1363 55 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 205
  (Polychromatic418967fa.accept_13_2_3_10_1_658 54 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 205 (accept_3_3 53 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 52 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 205 (Polychromatic418967fa.accept_21_9_7_16_1_5904 51 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 205 (accept_3_3 50 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 205 (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 205
  (Polychromatic418967fa.accept_10_8_3_5_1_613 48 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 205 (accept_3_3 47 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 205 (Polychromatic418967fa.accept_13_7_3_10_1_656 46 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 205 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 205 (accept_3_3 44 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 205 (Polychromatic418967fa.accept_21_1_7_16_1_5859 43 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 205
  (Polychromatic418967fa.accept_10_2_3_5_1_996 42 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 205 (accept_3_3 41 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 205 (Polychromatic418967fa.accept_14_12_7_9_1_726 40 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 205 (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 205 (accept_3_3 38 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 37 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 205
  (Polychromatic418967fa.accept_25_11_8_5_1_4696 36 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 205 (accept_3_3 35 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 205 (Polychromatic418967fa.accept_15_4_13_10_1_1508 34 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 205 (Polychromatic418967fa.accept_13_7_3_10_1_656 33 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 205 (accept_3_3 32 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 205 (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 205
  (Polychromatic418967fa.accept_14_2_7_9_1_2937 30 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 205 (accept_3_3 29 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 205 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 205 (accept_3_3 26 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 205 (Polychromatic418967fa.accept_16_9_5_13_1_4972 25 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 205
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 24 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 133 205 (accept_3_3 23 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 133 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 205 (Polychromatic418967fa.accept_17_4_14_1_1_1363 21 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 205 (accept_3_3 20 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 205
  (Polychromatic418967fa.accept_13_6_3_10_1_698 19 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 205 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 205 (accept_3_3 17 133 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 205 (Polychromatic418967fa.accept_14_2_7_9_1_2937 16 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 205
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 205 (accept_3_3 14 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 205 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 205 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 205 (accept_3_3 11 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 205 (Polychromatic418967fa.accept_16_10_5_13_1_8591 10 133
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 205
  (Polychromatic418967fa.accept_16_9_5_13_1_4972 9 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 205 (accept_3_3 8 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 205 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 205 (Polychromatic418967fa.accept_11_6_1_7_1_1315 6 133 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 205 (accept_3_3 5 133 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 205 (Polychromatic418967fa.accept_15_4_13_10_1_1508 4 133 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 205
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 205 (accept_3_3 2 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 205 (Polychromatic418967fa.accept_15_1_13_10_1_1507 1 133 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74
  132 205 (Eq.refl Bool.true) (allA_succ_of_accept 73 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 132 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 205
  (Polychromatic418967fa.accept_16_8_4_13_1_1014 72 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 132 205 (accept_3_3 71 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 132 205 (Polychromatic418967fa.accept_13_5_2_10_1_248 70 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 132 205 (Polychromatic418967fa.accept_15_9_12_10_1_809 69 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 205 (accept_3_3 68 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 67 132 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 66 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 132 205 (accept_3_3 65 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 64 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 132 205 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 205 (accept_3_3 62 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 205 (Polychromatic418967fa.accept_19_4_18_15_1_7899 61 132
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 205
  (Polychromatic418967fa.accept_7_4_6_2_1_451 60 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 132 205 (accept_3_3 59 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 132 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 205 (accept_3_3 56 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 205
  (Polychromatic418967fa.accept_15_9_12_10_1_809 54 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 132 205 (accept_3_3 53 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 132 205 (Polychromatic418967fa.accept_13_12_2_10_1_2698 51 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 205 (accept_3_3 50 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 49 132 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 205 (accept_3_3 47 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 205 (accept_3_3 44 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 205
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 42 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 205 (accept_3_3 41 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 132 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 205 (accept_3_3 38 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 37 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 205
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 132 205 (accept_3_3 35 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 132 205 (Polychromatic418967fa.accept_13_8_2_10_1_652 34 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 132 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 33 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 205 (accept_3_3 32 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 205 (accept_3_3 29 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 205 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 205 (accept_3_3 26 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 205
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 205 (accept_3_3 23 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 205 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 205 (accept_3_3 20 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 205 (Polychromatic418967fa.accept_9_1_6_7_1_285 19 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 205
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 205 (accept_3_3 17 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 205 (Polychromatic418967fa.accept_13_3_2_10_1_2697 16 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 205 (accept_3_3 14 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 205 (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 205
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 205 (accept_3_3 11 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 205 (Polychromatic418967fa.accept_8_1_4_5_1_48 9 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 205 (accept_3_3 8 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 205 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 205
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 6 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 205 (accept_3_3 5 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 205 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 132 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 205 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 205 (accept_3_3 2 132 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 205 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 131 205 (Eq.refl
  Bool.true) (allA_of_3_1 75 131 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 130 205 (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 130 205 5 15 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 130 205 (accept_3_3 74 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 130 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 73 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 205 (Polychromatic418967fa.accept_14_2_4_9_1_2121 72 130
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 130 205 (accept_3_3 71 130
  205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 130 205 5 14 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 130 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 130 205 (accept_3_3 68 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 130 205 (Polychromatic418967fa.accept_9_3_4_7_1_89 66 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 130 205 5 13 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 130 205
  (Polychromatic418967fa.accept_9_1_4_7_1_7 64 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 205 (accept_3_3 62 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 130 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 205 5 12 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 205 (accept_3_3 59 130 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 130 205 (Polychromatic418967fa.accept_14_2_4_9_1_2121 58 130
  205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 130 205 (accept_3_3 56 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  130 205 5 11 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 130 205 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 130 205 (accept_3_3 53 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 130 205 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 130 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 130 205 5 10 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 130 205 (Polychromatic418967fa.accept_11_5_9_7_1_411 49 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 205 (Polychromatic418967fa.accept_7_6_4_2_1_236
  48 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 130 205 (accept_3_3 47
  130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 130 205
  (Polychromatic418967fa.accept_9_1_4_7_1_7 46 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 130 205 5 9 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 130 205 (accept_3_3 44 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 130 205 (Polychromatic418967fa.accept_9_6_4_7_1_300 42 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 205 (accept_3_3 41 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 205 5 8 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 205 (accept_3_3 38 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 37
  130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 205
  (Polychromatic418967fa.accept_20_16_10_5_1_9133 36 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 130 205 5 7 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 130 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 130 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 205
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 130 205 (accept_3_3 32 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 205 5 6 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 205 (accept_3_3 29 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 130 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 205 (accept_3_3 26 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 130 205 5 5 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 130 205
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 205 (accept_3_3 23 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 205 (Polychromatic418967fa.accept_19_3_16_15_1_9281 22 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 205 5 4 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 205
  (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 130 205 (Polychromatic418967fa.accept_19_18_16_15_1_5044 18 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 205 (accept_3_3 17 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 205 (Polychromatic418967fa.accept_11_5_9_7_1_411 16 130 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 130 205 5 3 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 130 205 (accept_3_3 14 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 205 (Polychromatic418967fa.accept_7_6_4_2_1_236
  13 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 205
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 205 (accept_3_3 11 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  130 205 5 2 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 130 205 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 130 205 (accept_3_3 8 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 205 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 130 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 130 205 5 1 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 130 205
  (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 130 205 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 205 (accept_3_3 2 130 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 130 205 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 129 205 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 205 (Polychromatic418967fa.accept_7_5_3_2_1_249
  75 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 205 (accept_3_3 74
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 205
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 129 205 (Polychromatic418967fa.accept_13_7_12_10_1_640 72 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 205 (accept_3_3 71 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 205 (Polychromatic418967fa.accept_7_6_3_2_1_461
  69 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 205 (accept_3_3 68
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 205
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 129 205 (Polychromatic418967fa.accept_10_6_9_5_1_1046 66 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 205 (accept_3_3 65 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 205 (Polychromatic418967fa.accept_12_3_9_1_1_290
  63 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 205 (accept_3_3 62
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 129 205 (Polychromatic418967fa.accept_8_4_1_5_1_186 60 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 205 (accept_3_3 59 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 57
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 205 (accept_3_3 56
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 205
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 129 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 205 (accept_3_3 53 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 205 (Polychromatic418967fa.accept_9_6_3_7_1_580
  51 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 205 (accept_3_3 50
  129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 205
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 129 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 205 (accept_3_3 47 129 205 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 205
  (Polychromatic418967fa.accept_13_6_12_10_1_690 45 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 205 (accept_3_3 44 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 205 (accept_3_3 41 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 205 (accept_3_3 38 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 205 (Polychromatic418967fa.accept_9_1_3_7_1_6 37 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 205 (accept_3_3 35 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 205
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 205 (accept_3_3 32 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 205 (Polychromatic418967fa.accept_9_4_3_7_1_296 31 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 205 (Polychromatic418967fa.accept_16_14_1_13_1_2754 30 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 205 (accept_3_3 29 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 205
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 205 (accept_3_3 26 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 205 (Polychromatic418967fa.accept_16_9_1_13_1_1850 25 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 205 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 205 (accept_3_3 23 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 205
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 205 (accept_3_3 20 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 129 205 (Polychromatic418967fa.accept_15_3_9_10_1_2325 18 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 205 (accept_3_3 17 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 205
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 205 (accept_3_3 14 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 205 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 205 (accept_3_3 11 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 205
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 205 (accept_3_3 8 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 205 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 205 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 205 (accept_3_3 5 129 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 205 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 205
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 205 (accept_3_3 2 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 205 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 205))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 128 205 (Eq.refl Bool.true) (allA_of_3_1 78 128 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 127 205
  (Eq.refl Bool.true) (allA_succ_of_accept 78 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 205 (accept_3_3 77 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 76 127 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 75 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 205 (accept_3_3 74 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 73 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 205 (Polychromatic418967fa.accept_10_2_7_5_1_605 72 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 205 (accept_3_3 71 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 127 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 205 (accept_3_3 68 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 205 (accept_3_3 65 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 205 (Polychromatic418967fa.accept_14_8_1_9_1_2085 64 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 205
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 205 (accept_3_3 62 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 205 (Polychromatic418967fa.accept_9_6_1_7_1_577 60 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 205 (accept_3_3 59 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 57 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 205 (accept_3_3 56 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 205 (accept_3_3 53 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 205 (accept_3_3 50 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 205 (accept_3_3 47 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 205
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 205 (accept_3_3 44 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 205 (Polychromatic418967fa.accept_10_3_7_5_1_288 43 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 205 (accept_3_3 41 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 205 (accept_3_3 38 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 205 (Polychromatic418967fa.accept_23_14_12_21_1_11982 37 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 205 (Polychromatic418967fa.accept_14_8_1_9_1_2085 36 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 205 (accept_3_3 35 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 205
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 205 (accept_3_3 32 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 205 (accept_3_3 29 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 205 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 205
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 205 (accept_3_3 26 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 205 (Polychromatic418967fa.accept_19_6_13_15_1_2406 25 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 205 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 205 (accept_3_3 23 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 205
  (Polychromatic418967fa.accept_9_3_1_7_1_97 21 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 205 (accept_3_3 20 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 205 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 205 (accept_3_3 17 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 205 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 205
  (Polychromatic418967fa.accept_9_6_1_7_1_577 15 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 205 (accept_3_3 14 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 205 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 205 (Polychromatic418967fa.accept_9_3_1_7_1_97 12 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 205 (accept_3_3 11 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 205
  (Polychromatic418967fa.accept_17_9_8_1_1_7036 9 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 205 (accept_3_3 8 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 205 (Polychromatic418967fa.accept_17_7_8_1_1_1373 7 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 205 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 205 (accept_3_3 5 127 205 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 205 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 205 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 205
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 205 (accept_3_3 2 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 205 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 127 205 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 205)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_205_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


