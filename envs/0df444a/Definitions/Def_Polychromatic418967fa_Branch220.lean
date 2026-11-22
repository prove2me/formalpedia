-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch220
-- name    : Polychromatic418967fa_Branch220
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:26:08.931138+00:00
-- url     : https://prove2.me/theorems/2664ad0f-e1b7-4fdf-8017-b73f1f0159bb
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch220_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_220 : allB 220 220 :=
  allB_succ' 2 219 220 (Eq.refl Bool.true) (allA_succ_of_accept 1 219 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  219 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 219 220)) (allB_succ' 3 218 220
  (Eq.refl Bool.true) (allA_of_3_1 3 218 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 217 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 217 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 217 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 217 220 (accept_3_3 2 217 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 217 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 217 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 217 220)))) (allB_succ' 5 216 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 216 220 4 1 54 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 216 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 216 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 216 220 2 1 108 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045
  1 216 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 220))))) (allB_succ' 6 215 220
  (Eq.refl Bool.true) (allA_of_3_1 6 215 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 214 220 (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 214 220 2 3 107 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 214 220 (accept_3_3 5 214 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 214 220 2 2 107 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 214 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 214 220 2 1 107 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 214 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 214 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 214 220))))))) (allB_succ' 8 213 220 (Eq.refl Bool.true) (allA_succ_of_accept 7 213 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 213 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 213 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 213 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 213 220 (accept_3_3 5 213 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 213 220 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 213 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3
  213 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 220 (accept_3_3 2 213
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  1 213 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 220)))))))) (allB_succ' 9 212 220
  (Eq.refl Bool.true) (allA_of_3_1 9 212 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 211 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 9 211 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 211 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 211 220 (accept_3_3 8 211 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 211 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 211 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 211 220
  (Polychromatic418967fa.accept_15_6_1_10_1_1549 6 211 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 211 220 (accept_3_3 5 211 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  211 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 211 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 211 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 220 (accept_3_3 2 211 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 220 (Polychromatic418967fa.accept_28_1_15_24_1_13079 1 211 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 220)))))))))) (allB_succ' 11 210 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 210 220 10 1 21 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 210 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 210 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 210 220 2 4 105 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 210 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 210 220 2 3 105 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 5 210 220 5 1 42 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 4 210 220 2 2 105 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 210 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 210 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 220 2 1 105 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 210 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 220))))))))))) (allB_succ' 12 209 220 (Eq.refl Bool.true) (allA_of_3_1 12 209 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 208 220 (Eq.refl Bool.true) (allA_succ_of_gcd 12 208 220 4 3 52 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 208 220 (accept_3_3 11
  208 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 208 220 2 5 104 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 208 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 208 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 208 220 4 2 52 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 208 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 208 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 208 220 2 3 104 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 220 (accept_3_3 5 208 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 220 4 1 52 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 208 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 208 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 208 220 2 1 104 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 208 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 220))))))))))))) (allB_succ' 14 207 220 (Eq.refl Bool.true) (allA_succ_of_accept 13 207 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 207 220 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 207 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 207 220 (accept_3_3 11 207 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 207 220 (Polychromatic418967fa.accept_27_10_18_4_1_13078 10 207 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 220
  (Polychromatic418967fa.accept_15_9_12_10_1_809 9 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 207 220 (accept_3_3 8 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  207 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 207 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 220 (accept_3_3 5 207 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 220 (Polychromatic418967fa.accept_16_4_15_12_1_1745 4 207 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 220 (accept_3_3 2 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 207 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 220)))))))))))))) (allB_succ' 15 206 220 (Eq.refl Bool.true) (allA_of_3_1 15 206 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 205 220 (Eq.refl Bool.true) (allA_succ_of_gcd 15 205 220 5 3
  41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 205 220
  (accept_3_3 14 205 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 205 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 205 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 205 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 205 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 205 220 (accept_3_3 11 205 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 205 220 5 2 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 205 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 220 (accept_3_3 8 205 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 220 (Polychromatic418967fa.accept_13_7_10_12_1_2047 7 205
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 205 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 205 220 5 1 41 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 205 220 (Polychromatic418967fa.accept_16_4_13_12_1_1740 4 205 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 205 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 205 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 220 (accept_3_3 2 205 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  205 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 220)))))))))))))))) (allB_succ' 17
  204 220 (Eq.refl Bool.true) (allA_succ_of_gcd 16 204 220 4 4 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 204 220 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 204
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 204 220 2 7 102 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 220
  (Polychromatic418967fa.accept_24_13_12_4_1_2746 13 204 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 204 220 4 3 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 204 220 (accept_3_3 11 204 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 204 220 2 5 102 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 204 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 220 4 2 51 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7
  204 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 220 2 3 102 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 220 (accept_3_3 5
  204 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 220 4 1 51 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 204 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 204 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 204 220 2 1 102 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 204 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 1 204 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 220))))))))))))))))) (allB_succ' 18 203 220 (Eq.refl Bool.true)
  (allA_of_3_1 18 203 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 202 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 202 220 2 9 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 202 220 (accept_3_3 17 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 202 220 2 8 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 202 220 (Polychromatic418967fa.accept_25_15_2_20_1_13057 15 202 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 202 220 2 7 101 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 202 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 202 220 2 6 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 202 220 (accept_3_3 11 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 202 220 2 5 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 202 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 202 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 202 220 2 4 101 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 220 2 3 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 220 (accept_3_3 5 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 220 2 2 101 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 202 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 220 2 1 101 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 202 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 220))))))))))))))))))) (allB_succ' 20 201 220 (Eq.refl Bool.true) (allA_succ_of_accept 19 201 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 201 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 201 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 201 220 (accept_3_3 17 201 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 201 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 201 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 220 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 220 (accept_3_3 14
  201 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 201 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 220 (accept_3_3 11 201 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 201 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 201 220 (accept_3_3 8 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  201 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 201 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 6 201 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 220 (accept_3_3 5 201 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 220 (Polychromatic418967fa.accept_15_4_6_10_1_823 4 201 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 220
  (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 201 220 (accept_3_3 2 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  201 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 201 220)))))))))))))))))))) (allB_succ' 21 200 220 (Eq.refl Bool.true) (allA_of_3_1 21 200 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 199 220 (Eq.refl Bool.true) (allA_succ_of_accept 21 199 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 199 220 (accept_3_3 20 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 199 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 199 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058 18 199 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 199 220 (accept_3_3 17 199 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 199 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 199 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 199 220 (accept_3_3 14 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 199 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 199 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 199 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 220 (accept_3_3 11 199 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 199 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 199 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 199 220 (accept_3_3 8 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  199 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 199 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 199 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 220 (accept_3_3 5 199 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 4 199 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 220 (accept_3_3 2 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 220 (Polychromatic418967fa.accept_17_1_12_16_1_2211 1 199 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 220)))))))))))))))))))))) (allB_succ' 23 198 220 (Eq.refl Bool.true) (allA_succ_of_gcd 22
  198 220 22 1 9 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 198 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 198 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 198 220 2 10 99 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 198 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 198 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 198 220 2 9 99 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 198 220 (accept_3_3 17 198 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 198 220 2 8 99 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 198 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 198 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 198 220 2 7 99 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 198 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 198 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 220 2 6 99 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 198 220 11 1 18 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 198 220 2 5 99 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 198 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 198 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 198 220 2 4 99 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 198 220 (Polychromatic418967fa.accept_15_7_3_10_1_817 7 198 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 220 2 3 99 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 220 (accept_3_3 5 198 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 220 2 2 99 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 198 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 198 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 220 2 1 99 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 198 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 220))))))))))))))))))))))) (allB_succ' 24 197 220 (Eq.refl Bool.true) (allA_of_3_1 24 197 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 196 220 (Eq.refl Bool.true) (allA_succ_of_gcd 24 196 220 4 6 49 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 196 220
  (accept_3_3 23 196 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 196 220 2 11 98 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 196 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 196 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 196 220 4 5 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 196 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 196 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 196 220 2 9 98 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 196 220 (accept_3_3 17 196 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 196 220 4 4 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 196 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 196 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 220 2 7 98 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 220
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 196 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 220 4 3 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 196 220 (accept_3_3 11 196 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  196 220 2 5 98 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 196 220 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 196 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 220 4 2 49 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 7 196 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 196 220 2 3 98 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 220 (accept_3_3 5
  196 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 220 4 1 49 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 196 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 196 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 196 220 2 1 98 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 196 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 196 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 196 220))))))))))))))))))))))))) (allB_succ' 26 195 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 195 220 5 5 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 195 220 (Polychromatic418967fa.accept_16_8_3_12_1_1819 24 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 195 220 (accept_3_3 23 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 195 220 (Polychromatic418967fa.accept_26_22_13_12_1_7357 22 195 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 195 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 195 220 5 4 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 195 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 195 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 220 (accept_3_3 17 195 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 220 (Polychromatic418967fa.accept_7_2_6_3_1_100
  16 195 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 220 5 3 39 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 220
  (accept_3_3 14 195 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 195 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 195 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 12 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 220 (accept_3_3 11 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 195 220 5 2 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 195 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 195 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 220 (accept_3_3 8 195 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 195 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 195 220 5 1 39 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 195 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 195 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 195 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 220 (accept_3_3 2 195 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  195 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 220))))))))))))))))))))))))))
  (allB_succ' 27 194 220 (Eq.refl Bool.true) (allA_of_3_1 27 194 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 28 193 220 (Eq.refl Bool.true) (allA_succ_of_accept 27 193 220 (Polychromatic418967fa.accept_6_3_1_4_1_25
  27 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 193 220 (accept_3_3 26
  193 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 193 220
  (Polychromatic418967fa.accept_18_7_13_4_1_1670 25 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 193 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 24 193 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 193 220 (accept_3_3 23 193 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 193 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 193 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21
  193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 220 (accept_3_3 20
  193 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 220
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 19 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 193 220 (Polychromatic418967fa.accept_15_3_13_10_1_2332 18 193 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 220 (accept_3_3 17 193 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 193
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 220 (accept_3_3 14 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 12 193 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 220 (accept_3_3 11 193 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 193
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 220 (accept_3_3 8 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 220 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 193 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 220 (accept_3_3 5 193 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 220 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 193 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 220 (accept_3_3 2 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 193 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 220)))))))))))))))))))))))))))) (allB_succ' 29 192 220 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 192 220 4 7 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 192 220 (Polychromatic418967fa.accept_18_9_12_4_1_1659 27 192 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 192 220 2 13 96 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 192 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 25
  192 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 192 220 4 6 48 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 192 220 (accept_3_3 23
  192 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 220 2 11 96 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 220
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 192 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 192 220 4 5 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 192 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 19 192 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 220 2 9 96 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 220 (accept_3_3 17 192 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 220 4 4 48 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 192 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 220 2 7 96 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 192 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 220 4 3 48 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 220 (accept_3_3 11 192 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 220 2 5 96 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 220
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 192 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 220 4 2 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 192 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 220 2 3 96 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 220 (accept_3_3 5 192 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 220 4 1 48 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 220 (Polychromatic418967fa.accept_19_3_2_11_1_7647 3 192 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 220 2 1 96 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 1 192 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 220))))))))))))))))))))))))))))) (allB_succ' 30 191 220 (Eq.refl Bool.true) (allA_of_3_1 30 191 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 190 220 (Eq.refl Bool.true) (allA_succ_of_gcd 30 190 220 10 3
  19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 190 220
  (accept_3_3 29 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 190 220 2 14 95 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 190 220
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 190 220 2 13 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 25 190 220 5 5 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 190 220 2 12 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 190 220 (accept_3_3 23 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 220 2 11 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 190 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 220 10 2 19 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 220 2 9 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 220 (accept_3_3 17 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 220 2 8 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 190 220 5 3 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 190 220 2 7 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 190 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 190 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 190 220 2 6 95 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 190 220 (accept_3_3 11 190 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 220 10 1 19 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 190 220 2 4 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 190 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 190 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 190 220 2 3 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 190 220 5 1 38 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 190 220 2 2 95 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 190 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  190 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 190 220 2 1 95 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 190 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 190 220))))))))))))))))))))))))))))))) (allB_succ' 32 189 220 (Eq.refl Bool.true) (allA_succ_of_accept 31
  189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 189 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 30 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 189 220 (accept_3_3 29 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 189 220 (Polychromatic418967fa.accept_26_2_7_12_1_13077 28 189 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 189 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 27 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 220 (accept_3_3 26 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 24 189
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 220 (accept_3_3 23 189
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 220
  (Polychromatic418967fa.accept_17_5_2_16_1_1294 22 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 189 220 (Polychromatic418967fa.accept_13_8_7_12_1_3637 21 189 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 220 (accept_3_3 20 189 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 220 (Polychromatic418967fa.accept_12_6_9_4_1_96
  18 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 220 (accept_3_3 17
  189 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 220
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 16 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 189 220 (Polychromatic418967fa.accept_16_15_13_12_1_1787 15 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 220 (accept_3_3 14 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 220 (accept_3_3 11 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 10 189 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 220 (accept_3_3 8 189
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  7 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 220 (accept_3_3 5 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 220 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 189 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 189 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 220 (accept_3_3 2 189 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 220))))))))))))))))))))))))))))))))
  (allB_succ' 33 188 220 (Eq.refl Bool.true) (allA_of_3_1 33 188 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 34 187 220 (Eq.refl Bool.true) (allA_succ_of_gcd 33 187 220 11 3 17 20 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 187 220 (accept_3_3 32 187 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 187 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 187 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 187 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 187 220 (accept_3_3 29 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 187 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 187 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 220 (accept_3_3 26 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 220 (Polychromatic418967fa.accept_19_6_16_11_1_9041 25 187 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 220 (accept_3_3 23 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  187 220 11 2 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 187 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 187 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 220 (accept_3_3 20 187 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 187 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 220
  (Polychromatic418967fa.accept_15_3_7_10_1_2324 18 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 220 (accept_3_3 17 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 220 (accept_3_3 14 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 187 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 187 220 11 1 17 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 187 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9
  187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 220 (accept_3_3 8 187
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 220
  (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 187 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 6 187 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 220 (accept_3_3 5 187 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 187 220 (Polychromatic418967fa.accept_13_4_5_12_1_751 4 187 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3
  187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 220 (accept_3_3 2 187
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 187 220)))))))))))))))))))))))))))))))))) (allB_succ' 35 186 220 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  186 220 2 17 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 186 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 186 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 186 220 2 16 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 186 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058
  31 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 186 220 2 15 93 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 186 220
  (accept_3_3 29 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 220 2 14 93 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 220 2 13 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 25 186 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 186 220 2 12 93 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 186 220 (accept_3_3 23 186 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 220 2 11 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21
  186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 220 2 10 93 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 19 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 220 2 9 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 220 (accept_3_3 17 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 220 2 8 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 186 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 220 2 7 93 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 220 2 6 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 220 (accept_3_3 11 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 220 2 5 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 186 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 220 2 4 93 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 220 2 3 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 220 (accept_3_3 5 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  220 2 2 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 186 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 220 2 1 93 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 186 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 220))))))))))))))))))))))))))))))))))) (allB_succ'
  36 185 220 (Eq.refl Bool.true) (allA_of_3_1 36 185 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 184 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 184 220 4 9 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 184 220 (accept_3_3 35 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 184 220 2 17 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 184 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 184 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 184 220 4 8 46 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 184 220
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 184 220 2 15 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 184 220 (accept_3_3 29 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 184 220 4 7 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 184 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 184 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 220 2 13 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 220 (Polychromatic418967fa.accept_16_9_8_12_1_979
  25 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 220 4 6 46 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 220
  (accept_3_3 23 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 220 2 11 92 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 220
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 21 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 184 220 4 5 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 184 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 184 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 220 2 9 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 220 (accept_3_3 17 184 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 220 4 4 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 184 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 220 2 7 92 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 220 4 3 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 184 220 (accept_3_3 11 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  184 220 2 5 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 184 220 (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 184 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 220 4 2 46 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 184 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 220 2 3 92 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 220 (accept_3_3 5
  184 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 220 4 1 46 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 220
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 184 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 184 220 2 1 92 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 184 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 184 220))))))))))))))))))))))))))))))))))))) (allB_succ' 38 183 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 183 220
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 183 220 (accept_3_3 35 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 183 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 183 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 183 220 (accept_3_3 32 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 220 (accept_3_3 29 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 220 (accept_3_3 26 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 220 (accept_3_3 23 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 220 (Polychromatic418967fa.accept_15_7_3_10_1_817 22 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 220 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 220 (accept_3_3 20 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 220 (accept_3_3 17 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 220 (accept_3_3 14 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 220 (accept_3_3 11 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 220 (accept_3_3 8 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 220 (accept_3_3 5 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 220 (accept_3_3 2 183 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 183 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 220))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 182 220 (Eq.refl Bool.true) (allA_of_3_1 39 182 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 181 220 (Eq.refl Bool.true) (allA_succ_of_accept 39 181 220 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 181 220 (accept_3_3 38
  181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 181 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 181 220 (Polychromatic418967fa.accept_15_6_1_10_1_1549 36 181 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 220 (accept_3_3 35 181 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 181 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33
  181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 220 (accept_3_3 32
  181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 220
  (Polychromatic418967fa.accept_14_3_13_10_1_761 31 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 181 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 181 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 220 (accept_3_3 29 181 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 181 220 (Polychromatic418967fa.accept_15_13_1_10_1_816 28 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 220 (accept_3_3 26 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 220 (accept_3_3 23 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 220 (accept_3_3 20 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 220 (Polychromatic418967fa.accept_25_19_6_20_1_13076 19 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 220 (accept_3_3 17 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 181 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 220 (accept_3_3 14 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 220 (Polychromatic418967fa.accept_15_13_1_10_1_816 13 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 220 (accept_3_3 11 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 220 (accept_3_3 8 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 220 (accept_3_3 5 181 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 220 (accept_3_3 2 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 220)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 180 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 180 220 20 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 180 220 (Polychromatic418967fa.accept_16_7_4_12_1_1806 39 180 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 180 220 2 19 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 180 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 37
  180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 180 220 4 9 45 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 180 220 5 7 36 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 220 2 17 90 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 220
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 180 220 4 8 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 180 220 (Polychromatic418967fa.accept_16_15_4_12_1_2731 31 180 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 220 10 3 18 22 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 220 (accept_3_3 29
  180 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 220 4 7 45 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 220
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 180 220 2 13 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 25 180 220 5 5 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 180 220 4 6 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 220 (accept_3_3 23 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 220 2 11 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 180 220 (Polychromatic418967fa.accept_16_5_4_12_1_3800 21 180 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 220 20 1 9 11 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 220
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 180 220 2 9 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 180 220 (accept_3_3 17 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 220 4 4 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 180 220 5 3 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 180 220 2 7 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 220 (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 180 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 220 4 3 45 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 220 (accept_3_3 11 180 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 220 10 1 18 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 220 4 2 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 220 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 180 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 220 2 3 90 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 220 5 1 36 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 180 220 4 1 45 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 220 (Polychromatic418967fa.accept_16_3_4_12_1_3799
  3 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 220 2 1 90 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 220))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 179 220 (Eq.refl Bool.true) (allA_of_3_1 42
  179 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 178 220 (Eq.refl Bool.true) (allA_succ_of_gcd 42 178
  220 2 21 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 178 220 (accept_3_3 41 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 178 220 2 20 89 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 178 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 178 220 2 19 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 178 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 178 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 178 220 2 18 89 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 178 220 (accept_3_3 35 178 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 178 220 2 17 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 178 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 220 2 16 89 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 220 2 15 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 220 (accept_3_3 29 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 220 2 14 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 27 178 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 220 2 13 89 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 220 2 12 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 220 (accept_3_3 23 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 220 2 11 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 178 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 220 2 10 89 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 220 2 9 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 220 (accept_3_3 17 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 220 2 8 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 178 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 220 2 7 89 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 220 2 6 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 220 (accept_3_3 11 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 220 2 5 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 220 (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 178 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 220 2 4 89 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 220 2 3 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 220 (accept_3_3 5 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  220 2 2 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 178 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 220 2 1 89 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 178 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 220)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 177 220 (Eq.refl Bool.true) (allA_succ_of_accept 43 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 177 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 177 220 (accept_3_3 41 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 177 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 177 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 220 (accept_3_3 38 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 220 (accept_3_3 35 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 220 (accept_3_3 32 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 30 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 220 (accept_3_3 29 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 220 (accept_3_3 26 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 220
  (Polychromatic418967fa.accept_15_9_12_10_1_809 24 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 220 (accept_3_3 23 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 220 (accept_3_3 20 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 220 (accept_3_3 17 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 220 (accept_3_3 14 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 220 (accept_3_3 11 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 220 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 220 (accept_3_3 8 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 220 (accept_3_3 5 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 177 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 220 (accept_3_3 2 177 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 220))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 176 220 (Eq.refl Bool.true) (allA_of_3_1 45 176 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 175 220 (Eq.refl Bool.true) (allA_succ_of_gcd 45 175 220 5 9 35 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 175 220 (accept_3_3 44 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 175 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 175 220
  (Polychromatic418967fa.accept_28_14_7_24_1_13075 42 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 175 220 (accept_3_3 41 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 175 220 5 8 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 175 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 220 (accept_3_3 38 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 175 220 (Polychromatic418967fa.accept_19_18_4_11_1_11751 37 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 175 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 175 220 5 7 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 175 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 220 (accept_3_3 32 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 220 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 175 220 5 6 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 175 220 (accept_3_3 29 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 175 220 (Polychromatic418967fa.accept_13_2_6_12_1_1334 28 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 220 (accept_3_3 26 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 175 220 5 5 35 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 175 220
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 175 220 (accept_3_3 23 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 175 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 175 220 5 4 35 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 19 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 220 (Polychromatic418967fa.accept_13_5_6_12_1_2750 18 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 220 (accept_3_3 17 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 220 (Polychromatic418967fa.accept_19_16_4_11_1_11756 16 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 220 5 3 35 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 175 220 (accept_3_3 14 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 220
  (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 220 (Polychromatic418967fa.accept_19_12_4_11_1_6078 12 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 220 (accept_3_3 11 175 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 175 220 5 2 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 175 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9
  175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 220 (accept_3_3 8 175
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 220
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 175 220 (Polychromatic418967fa.accept_26_6_19_12_1_13074 6 175 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 220 5 1 35 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 175 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 220 (accept_3_3 2 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 220 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 175 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 220)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 174 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 174 220 2 23 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 174 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 174 220 2 22 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 43 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 220 2 21 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 220 (accept_3_3 41 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 174 220 2 20 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 220 2 19 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 220 2 18 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 220 (accept_3_3 35 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 220 2 17 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 220 2 16 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 220
  (Polychromatic418967fa.accept_14_3_6_10_1_752 31 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 220 2 15 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 220 (accept_3_3 29 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 220 2 14 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 220 2 13 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 220 2 12 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 220 (accept_3_3 23 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 220 2 11 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 220 2 10 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 220 2 9 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 220 (accept_3_3 17 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 220 2 8 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 220 2 7 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 220
  (Polychromatic418967fa.accept_19_13_3_11_1_4706 13 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 174 220 2 6 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 174 220 (accept_3_3 11 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 220 2 5 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 174 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 220 2 4 87 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 220 2 3 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 220 (accept_3_3 5 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  220 2 2 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 174 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 220 2 1 87 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 174 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 220)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 173 220 (Eq.refl Bool.true) (allA_of_3_1 48 173 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 172 220 (Eq.refl Bool.true) (allA_succ_of_gcd 48 172 220 4 12 43 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 172 220 (accept_3_3 47 172 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 172 220 2 23 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 172 220
  (Polychromatic418967fa.accept_27_18_10_4_1_13073 45 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 172 220 4 11 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 172 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 172 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 172 220 2 21 86 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 172 220 (accept_3_3 41 172 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 172 220 4 10 43 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 172 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 172 220 2 19 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 172 220 (Polychromatic418967fa.accept_19_18_1_11_1_10478 37 172 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 172 220 4 9 43 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 172 220 (accept_3_3 35 172 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 172 220 2 17 86 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 172 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 33 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 172 220 4 8 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 172 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 172 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 172 220 2 15 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 172 220 (accept_3_3 29 172 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 172 220 4 7 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 172 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 172 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 220 2 13 86 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 220 4 6 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 172 220 (accept_3_3 23 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  172 220 2 11 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 172 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 172 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 220 4 5 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 220 (Polychromatic418967fa.accept_15_4_7_10_1_807
  19 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 172 220 2 9 86 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 172 220
  (accept_3_3 17 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 172 220 4 4 43 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 172 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 172 220 2 7 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 172 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 220 4 3 43 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 220 (accept_3_3 11 172 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 220 2 5 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 220 (Polychromatic418967fa.accept_13_9_3_12_1_2025
  9 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 220 4 2 43 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 7 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 220 2 3 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 220 (accept_3_3 5 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  220 4 1 43 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 172 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 220 2 1 86 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 172 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 220)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 171 220 (Eq.refl Bool.true) (allA_succ_of_accept 49 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 220
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 171 220 (accept_3_3 47 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 171 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 46 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 171 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 220 (accept_3_3 44 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 171 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 220 (accept_3_3 41 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 40 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 171 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 220 (accept_3_3 38 171 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 220
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 36 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 220 (accept_3_3 35 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 220 (Polychromatic418967fa.accept_14_6_3_10_1_3905 34 171 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 33 171
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 220 (accept_3_3 32 171
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 220 (accept_3_3 29 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 220 (Polychromatic418967fa.accept_21_7_3_10_1_13044 28 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 220 (accept_3_3 26 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 171 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 220
  (Polychromatic418967fa.accept_16_8_11_12_1_962 24 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 220 (accept_3_3 23 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 220 (Polychromatic418967fa.accept_17_5_1_16_1_4359 22 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 220 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 220 (accept_3_3 20 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 220 (accept_3_3 17 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 220 (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 171 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 220 (accept_3_3 14 171 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 220
  (Polychromatic418967fa.accept_15_12_6_10_1_1516 12 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 220 (accept_3_3 11 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 220 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 171 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 220 (Polychromatic418967fa.accept_21_9_3_10_1_8573
  9 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 220 (accept_3_3 8
  171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 171 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 6 171 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 220 (accept_3_3 5 171 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 171 220 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 171 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 220
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 3 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 220 (accept_3_3 2 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 220)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 170 220 (Eq.refl
  Bool.true) (allA_of_3_1 51 170 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 169 220 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 169 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 169 220 (accept_3_3 50 169 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 169 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 49 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 169 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 169 220 (accept_3_3 47 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 169 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 169 220 (accept_3_3 44 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 169 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 169 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 169 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 169 220 (accept_3_3 41 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 169 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 169 220 (accept_3_3 38 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 169 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 220
  (Polychromatic418967fa.accept_15_6_4_10_1_2319 36 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 169 220 (accept_3_3 35 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 169 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 220 (accept_3_3 32 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 169 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 31 169 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 169 220 (accept_3_3 29 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 169 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 220 (accept_3_3 26 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 220 (accept_3_3 23 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 220 (accept_3_3 20 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 220 (accept_3_3 17 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 220 (accept_3_3 14 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 220 (accept_3_3 11 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 220 (accept_3_3 8 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 7 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 220 (accept_3_3 5 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 220 (accept_3_3 2 169 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169
  220)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 168 220 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 168 220 4 13 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 168 220 (Polychromatic418967fa.accept_15_6_3_10_1_2341 51 168 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 168 220 2 25 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 220 (Polychromatic418967fa.accept_16_1_8_12_1_405
  49 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 220 4 12 42 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 220
  (accept_3_3 47 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 220 2 23 84 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 220
  (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 168 220 4 11 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 168 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 168 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 220 2 21 84 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 220 (accept_3_3 41 168 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 220 4 10 42 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 39 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 220 2 19 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 37 168 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 220 4 9 42 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 220 (accept_3_3 35 168 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 220 2 17 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 220 (Polychromatic418967fa.accept_16_1_8_12_1_405
  33 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 220 4 8 42 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 220
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 31 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 168 220 2 15 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 168 220 (accept_3_3 29 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 220 4 7 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 220 (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 168 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 220 2 13 84 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 220 4 6 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 220 (accept_3_3 23 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  168 220 2 11 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 168 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 168 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 220 4 5 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 19
  168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 220 2 9 84 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 220 (accept_3_3 17
  168 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 220 4 4 42 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 220
  (Polychromatic418967fa.accept_16_15_8_12_1_2737 15 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 220 2 7 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 220 (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 168 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 220 4 3 42 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 220 (accept_3_3 11
  168 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 220 2 5 84 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 220
  (Polychromatic418967fa.accept_15_9_3_10_1_2312 9 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 220 4 2 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 220 2 3 84 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 220 (accept_3_3 5 168 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 220 4 1 42 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 220 2 1 84 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 168 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 220))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 167 220 (Eq.refl Bool.true)
  (allA_of_3_1 54 167 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 166 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 54 166 220 2 27 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 166 220 (accept_3_3 53 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 166 220 2 26 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 166 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 166 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 166 220 2 25 83 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 166 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 166 220 2 24 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 166 220 (accept_3_3 47 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 166 220 2 23 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 166 220 (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 220 2 22 83 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 220 2 21 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 220 (accept_3_3 41 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 220 2 20 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 220 (Polychromatic418967fa.accept_15_9_1_10_1_4316 39 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 220 2 19 83 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 220 2 18 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 220 (accept_3_3 35 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 220 2 17 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 220 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 220 2 16 83 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 220 2 15 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 220 (accept_3_3 29 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 220 2 14 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 220 (Polychromatic418967fa.accept_60_27_46_40_1_13072 27 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 220 2 13 83 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 220 2 12 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 220 (accept_3_3 23 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 220 2 11 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 220 (Polychromatic418967fa.accept_13_8_10_12_1_1337 21 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 220 2 10 83 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 220 2 9 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 220 (accept_3_3 17 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 220 2 8 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 166 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 220 2 7 83 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 13 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 220 2 6 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 220 (accept_3_3 11 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 220 2 5 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 220 2 4 83 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 220 2 3 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 220 (accept_3_3 5 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  220 2 2 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 220 (Polychromatic418967fa.accept_17_3_13_16_1_2183 3 166 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 220 2 1 83 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 166 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 165 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 165 220 55 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 165 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 54 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 220 (accept_3_3 53 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 165 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 165 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 220 (Polychromatic418967fa.accept_9_6_3_4_1_477
  51 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 165 220 5 10 33 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 165 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 49 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 165 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 220 (accept_3_3 47 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 165 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 165 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 220 5 9 33 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 165 220 11 4 15 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 165 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 43 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 42 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 220 (accept_3_3 41 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 165 220 5 8 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 165 220 (Polychromatic418967fa.accept_16_7_5_12_1_4824 39 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 220 (accept_3_3 38 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 165 220 5 7 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 165 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 220 11 3 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 220 (accept_3_3 32 165 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 220 5 6 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 220 (accept_3_3 29 165 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28
  165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 220 (accept_3_3 26 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  165 220 5 5 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 165 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 24 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 220 (accept_3_3 23 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 165 220 11 2 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 165 220 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 220 5 4 33 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 165 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 220 (accept_3_3 17 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 165 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 220 5 3 33 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 220 (accept_3_3 14 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 220
  (Polychromatic418967fa.accept_19_12_13_11_1_453 12 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 11 165 220 11 1 15 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 165 220 5 2 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 165 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 220 (accept_3_3 8 165 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 165 220 5 1 33 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 165 220 (Polychromatic418967fa.accept_16_4_5_12_1_2749 4 165 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 165
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 220 (accept_3_3 2 165 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  165 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 164 220 (Eq.refl Bool.true) (allA_of_3_1 57
  164 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 163 220 (Eq.refl Bool.true) (allA_succ_of_accept 57
  163 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 163 220 (accept_3_3 56 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 163 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 163 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 163 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 163 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 163 220 (accept_3_3 53 163 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 163 220 (Polychromatic418967fa.accept_9_7_1_4_1_217
  52 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 163 220 (accept_3_3 50 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 163 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 220 (accept_3_3 47 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 46 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 220 (accept_3_3 44 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 220 (accept_3_3 41 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 220 (accept_3_3 38 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 220 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 220 (accept_3_3 35 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 220 (accept_3_3 32 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 220 (accept_3_3 29 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 220 (Polychromatic418967fa.accept_21_7_16_10_1_1349 28 163 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 220 (accept_3_3 26 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 220 (accept_3_3 23 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 220 (accept_3_3 20 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 220 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 220 (accept_3_3 17 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 220 (accept_3_3 14 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 220 (accept_3_3 11 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 220 (accept_3_3 8 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 220 (accept_3_3 5 163 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 220 (Polychromatic418967fa.accept_13_4_7_12_1_2823 4 163 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 220 (accept_3_3 2 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 162 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 58 162 220 2 29 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 162 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 162 220 2 28 81 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 220
  (Polychromatic418967fa.accept_16_7_2_12_1_1754 55 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 220 2 27 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 220 (accept_3_3 53 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 162 220 2 26 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 162 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 220 2 25 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 162 220 2 24 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 162 220 (accept_3_3 47 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 220 2 23 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 220 2 22 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 220
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 43 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 162 220 2 21 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 162 220 (accept_3_3 41 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 162 220 2 20 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 162 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 162 220 2 19 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 162 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 220 2 18 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 220 (accept_3_3 35 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 162 220 2 17 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 162 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 220 2 16 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 220
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 220 2 15 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 220 (accept_3_3 29 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 220 2 14 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 220 2 13 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 220 2 12 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 220 (accept_3_3 23 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 220 2 11 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 220 2 10 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 220 2 9 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 220 (accept_3_3 17 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 220 2 8 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 220 2 7 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 220
  (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 162 220 2 6 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 162 220 (accept_3_3 11 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 220 2 5 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 162 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 220 2 4 81 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 220
  (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 220 2 3 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 220 (accept_3_3 5 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  220 2 2 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 162 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 220 2 1 81 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 220 (Polychromatic418967fa.accept_16_1_2_12_1_1757 1 162 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 161 220 (Eq.refl Bool.true) (allA_of_3_1
  60 161 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 160 220 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  160 220 20 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  59 160 220 (accept_3_3 59 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 160 220 2 29 80 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 160 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 57 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 160 220 4 14 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 160 220 5 11 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 160 220 2 27 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 160 220 (accept_3_3 53 160 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 160 220 4 13 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 160 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 160 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 160 220 10 5 16 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 160 220
  (Polychromatic418967fa.accept_21_7_13_10_1_8604 49 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 160 220 4 12 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 160 220 (accept_3_3 47 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 160 220 2 23 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 160 220 5 9 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 160 220 4 11 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 160 220 (Polychromatic418967fa.accept_18_7_16_4_1_1674 43 160 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 220 2 21 80 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 220 (accept_3_3 41 160 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 220 20 2 8 11 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 160 220 2 19 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 160 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 160 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 220 4 9 40 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 160 220 5 7 32 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 34 160 220 2 17 80 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 33 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 160 220 4 8 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 160 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058 31 160 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 220 10 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 220 (accept_3_3 29 160 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 160 220 4 7 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 160 220 (Polychromatic418967fa.accept_17_10_7_16_1_6841 27 160
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 220 2 13 80 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 160 220 5 5 32 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 220 4 6 40 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 220 (accept_3_3 23
  160 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 220 2 11 80 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 21 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 220 20 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 160 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 220 2 9 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 220 (accept_3_3 17 160 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 220 4 4 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 160 220 5 3 32 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 160 220 2 7 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 220
  (Polychromatic418967fa.accept_26_13_4_12_1_13071 13 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 160 220 4 3 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 160 220 (accept_3_3 11 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 220 10 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 220 4 2 40 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 220 (Polychromatic418967fa.accept_13_7_4_12_1_1341
  7 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 220 2 3 80 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 160 220 5 1 32 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 160 220 4 1 40 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 3 160 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 160 220 2 1 80 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 160 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 160 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 160 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 159 220 (Eq.refl Bool.true) (allA_succ_of_accept 61 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  61 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 220
  (Polychromatic418967fa.accept_17_9_6_16_1_3280 60 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 159 220 (accept_3_3 59 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 159 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 159 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 220 (accept_3_3 56 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 220 (accept_3_3 53 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 159 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 220 (accept_3_3 50 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 220 (accept_3_3 47 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 46 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 220 (Polychromatic418967fa.accept_16_13_15_12_1_1748 45 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 220 (accept_3_3 44 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 42 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 220 (accept_3_3 41 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 220 (accept_3_3 38 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 220 (accept_3_3 35 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 220 (accept_3_3 32 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 220 (accept_3_3 29 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 220 (accept_3_3 26 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 220
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 220 (accept_3_3 23 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 159 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 220 (accept_3_3 20 159 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 220 (accept_3_3 17 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 220 (accept_3_3 14 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 220 (accept_3_3 11 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 220 (accept_3_3 8 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 220 (accept_3_3 5 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 220 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 159 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 220 (accept_3_3 2 159 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 158 220 (Eq.refl Bool.true)
  (allA_of_3_1 63 158 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 157 220 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 157 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 157 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 157 220 (accept_3_3 62 157 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 157 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 61 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 157 220
  (Polychromatic418967fa.accept_13_8_1_12_1_762 60 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 157 220 (accept_3_3 59 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 157 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 157 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 157 220 (accept_3_3 56 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 157 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 55 157 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 220
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 157 220 (accept_3_3 53 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 157 220 (Polychromatic418967fa.accept_16_4_13_12_1_1740 52 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 157 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 220 (accept_3_3 50 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 157 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 220
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 220 (accept_3_3 47 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 220 (accept_3_3 44 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 43 157 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 220
  (Polychromatic418967fa.accept_15_12_7_10_1_3297 42 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 157 220 (accept_3_3 41 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 157 220 (Polychromatic418967fa.accept_16_8_13_12_1_3809 40 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39
  157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 220 (accept_3_3 38
  157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 220
  (Polychromatic418967fa.accept_13_11_1_12_1_742 37 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 157 220 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 220 (accept_3_3 35 157 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 220 (accept_3_3 32 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 220 (Polychromatic418967fa.accept_13_5_1_12_1_740 31 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 220 (Polychromatic418967fa.accept_23_7_19_13_1_13070 30 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 220 (accept_3_3 29 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 220 (Polychromatic418967fa.accept_13_2_1_12_1_1326 28 157
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 220 (accept_3_3 26 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 220 (accept_3_3 23 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 157
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 220 (accept_3_3 20 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 220 (Polychromatic418967fa.accept_15_4_7_10_1_807 19 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 220 (Polychromatic418967fa.accept_13_5_1_12_1_740 18 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 220 (accept_3_3 17 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 16 157
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 220 (accept_3_3 14 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 220 (Polychromatic418967fa.accept_15_12_7_10_1_3297 12 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 220 (accept_3_3 11 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 157
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 220 (accept_3_3 8 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 220 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 220 (Polychromatic418967fa.accept_14_6_3_10_1_3905 6 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 220 (accept_3_3 5 157 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 220 (Polychromatic418967fa.accept_15_4_7_10_1_807 4 157 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 220 (accept_3_3 2 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 157 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 156 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 156 220 4 16 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 156
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 156 220 2 31 78 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 156 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 220 4 15 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 220 (accept_3_3 59 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 156 220 2 29 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 156 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 220 4 14 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 220 2 27 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 220 (accept_3_3 53 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 220 4 13 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 156 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 220 2 25 78 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 220
  (Polychromatic418967fa.accept_15_4_6_10_1_823 49 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 220 4 12 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 220 (accept_3_3 47 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 220 2 23 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 220 (Polychromatic418967fa.accept_18_9_12_4_1_1659 45 156 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 220 4 11 39 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 220 2 21 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 220 (accept_3_3 41 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 220 4 10 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 220 (Polychromatic418967fa.accept_21_18_9_10_1_2571 39 156 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 220 2 19 78 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 37 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 220 4 9 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 220 (accept_3_3 35 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  156 220 2 17 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 156 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 220 4 8 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 220 (Polychromatic418967fa.accept_15_1_6_10_1_23
  31 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 220 2 15 78 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 220
  (accept_3_3 29 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 220 4 7 39 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 220 2 13 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 25 156 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 220 4 6 39 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 220 (accept_3_3 23 156 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 220 2 11 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 220 (Polychromatic418967fa.accept_17_4_3_16_1_9483
  21 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 220 4 5 39 55
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 220 2 9 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 220 (accept_3_3 17 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 220 4 4 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 156 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 220 2 7 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 220 4 3 39 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 220 (accept_3_3 11
  156 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 220 2 5 78 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 220
  (Polychromatic418967fa.accept_18_9_12_4_1_1659 9 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 220 4 2 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 220 2 3 78 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 220 (accept_3_3 5 156 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 220 4 1 39 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 3 156 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 220 2 1 78 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 155 220 (Eq.refl
  Bool.true) (allA_of_3_1 66 155 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 154 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 154 220 22 3 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 154 220 (accept_3_3 65 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64
  154 220 2 32 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 154 220 (Polychromatic418967fa.accept_17_12_1_16_1_4360 63 154 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 154 220 2 31 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 154 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 154 220 2 30 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 154 220 (accept_3_3 59 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 154 220 2 29 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 154 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 154 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 220 2 28 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 154 220 11 5 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 154 220 2 27 77 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 220 (accept_3_3 53
  154 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 220 2 26 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 51 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 220 2 25 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 154 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 154 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 154 220 2 24 77 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 220 (accept_3_3 47 154 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 154 220 2 23 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 154 220
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 45 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 154 220 22 2 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 154 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 43 154 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 154 220 2 21 77 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 154 220 (accept_3_3 41 154 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 154 220 2 20 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 154 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 39 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 154 220 2 19 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 154 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 37 154 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 154 220 2 18 77 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 154 220 (accept_3_3 35 154 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 154 220 2 17 77 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 154 220 11 3 14 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 154 220 2 16 77 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 220 2 15 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 220 (accept_3_3 29 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 220 2 14 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 220 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 154 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 220 2 13 77 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 220 2 12 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 220 (accept_3_3 23 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 220 22 1 7 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 154 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 154 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 220 2 10 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 220 (Polychromatic418967fa.accept_12_7_10_4_1_382
  19 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 220 2 9 77 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 220
  (accept_3_3 17 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 220 2 8 77 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 15 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 220 2 7 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 154 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 154 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 220 2 6 77 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 154 220 11 1 14 20 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 154 220 2 5 77 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 220
  (Polychromatic418967fa.accept_15_9_4_10_1_2316 9 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 220 2 4 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 220 2 3 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 220 (accept_3_3 5 154 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154 220 2 2 77 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 154 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 154 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 220 2 1 77 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 1 154 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 153 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 153 220 (Polychromatic418967fa.accept_12_6_9_4_1_96
  66 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 220 (accept_3_3 65
  153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 220
  (Polychromatic418967fa.accept_24_16_9_4_1_13069 64 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 153 220 (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 220 (accept_3_3 62 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 60 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 153 220 (accept_3_3 59 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 153 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 153 220 (Polychromatic418967fa.accept_21_15_6_10_1_10016 57 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 220 (accept_3_3 56 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 153 220 (accept_3_3 53 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 153 220 (Polychromatic418967fa.accept_15_7_3_10_1_817 52 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 153 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 220 (accept_3_3 50 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 220
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 220 (accept_3_3 47 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 153 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 220 (accept_3_3 44 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43
  153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 220 (accept_3_3 41 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 220 (Polychromatic418967fa.accept_16_8_9_12_1_1737 40 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 220 (accept_3_3 38 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 220
  (Polychromatic418967fa.accept_15_6_3_10_1_2341 36 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 220 (accept_3_3 35 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 220 (Polychromatic418967fa.accept_13_8_10_12_1_1337 34 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 220 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 220 (accept_3_3 32 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 220 (accept_3_3 29 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 220 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 220 (Polychromatic418967fa.accept_19_8_1_11_1_4718 27 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 220 (accept_3_3 26 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 220
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 220 (accept_3_3 23 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 220 (Polychromatic418967fa.accept_13_9_10_12_1_2048 22 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 220 (Polychromatic418967fa.accept_8_5_1_4_1_628
  21 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 220 (accept_3_3 20
  153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 153 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 153 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 220 (accept_3_3 17 153 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 153 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 220
  (Polychromatic418967fa.accept_13_2_10_12_1_757 15 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 220 (accept_3_3 14 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 220 (Polychromatic418967fa.accept_18_12_9_4_1_2740 12 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 220 (accept_3_3 11 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 220 (Polychromatic418967fa.accept_19_10_1_11_1_7532 10 153
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 220 (accept_3_3 8 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 220 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 220 (accept_3_3 5 153 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 220
  (Polychromatic418967fa.accept_14_3_13_10_1_761 3 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 220 (accept_3_3 2 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 152
  220 (Eq.refl Bool.true) (allA_of_3_1 69 152 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 151 220
  (Eq.refl Bool.true) (allA_succ_of_accept 69 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 151 220 (accept_3_3 68 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 151 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 67 151 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 151 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 151 220 (accept_3_3 65 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 151 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 220 (accept_3_3 62 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 151 220 (Polychromatic418967fa.accept_13_9_8_12_1_2031 61 151 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 151 220 (accept_3_3 59 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 151 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 58 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 220 (accept_3_3 56 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 220
  (Polychromatic418967fa.accept_15_9_1_10_1_4316 54 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 220 (accept_3_3 53 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 220 (Polychromatic418967fa.accept_15_7_1_10_1_305 52 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 220 (accept_3_3 50 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 220 (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 151 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 220 (accept_3_3 47 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 220 (accept_3_3 44 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 220 (accept_3_3 41 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 220 (Polychromatic418967fa.accept_13_1_8_12_1_2045 40 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 220 (accept_3_3 38 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 220 (accept_3_3 35 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 220 (accept_3_3 32 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 220 (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 151 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 220 (accept_3_3 29 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 220 (accept_3_3 26 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 220 (Polychromatic418967fa.accept_19_6_18_11_1_7636 25 151 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 220 (accept_3_3 23 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 220 (accept_3_3 20 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 220
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 18 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 220 (accept_3_3 17 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 220 (Polychromatic418967fa.accept_18_16_7_4_1_3901 16 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 220 (accept_3_3 14 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 220 (accept_3_3 11 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 220 (accept_3_3 8 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 220 (Polychromatic418967fa.accept_13_7_8_12_1_2810 7 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 220 (accept_3_3 5 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 220 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 151 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 220 (accept_3_3 2 151 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 150 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 150 220 10 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 150 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 150 220 2 34 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 150 220
  (Polychromatic418967fa.accept_28_11_10_24_1_13068 67 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 150 220 2 33 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 65 150 220 5 13 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 64 150 220 2 32 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 220 (Polychromatic418967fa.accept_12_3_6_4_1_400
  63 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 220 2 31 75 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 220 10 6 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 220 (accept_3_3 59 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 220 2 29 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 220 2 28 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 150 220 5 11 30 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 150 220 2 27 75 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 220 (accept_3_3 53
  150 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 220 2 26 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 220
  (Polychromatic418967fa.accept_12_3_6_4_1_400 51 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 220 10 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 220 (Polychromatic418967fa.accept_13_10_7_12_1_2782 49 150 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 150 220 2 24 75 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 150 220 (accept_3_3 47 150 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 220 2 23 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 220 5 9 30 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 220 2 22 75 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 43 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 220 2 21 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 220 (accept_3_3 41 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 220 10 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 39 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 220 2 19 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 37 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 220 2 18 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 150 220 5 7 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 150 220 2 17 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 150 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 150 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 220 2 16 75 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 220
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 220 10 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 220 (accept_3_3 29 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 220 2 14 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 220 2 13 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 150 220 5 5 30 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 220 2 12 75 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 220 (accept_3_3 23 150 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 220 2 11 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 21 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 220 10 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 220 2 9 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 220 (accept_3_3 17 150 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 220 2 8 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 220 5 3 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 220 2 7 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 220
  (Polychromatic418967fa.accept_19_13_17_11_1_4716 13 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 150 220 2 6 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 150 220 (accept_3_3 11 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 220 10 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 150 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 220 2 4 75 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 220 2 3 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 150 220 5 1 30 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 150 220 2 2 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 150 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 220 2 1 75 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  150 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 149 220 (Eq.refl Bool.true)
  (allA_of_3_1 72 149 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 148 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 148 220 4 18 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 148 220 (accept_3_3 71 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 148 220 2 35 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 148 220 (Polychromatic418967fa.accept_13_4_5_12_1_751 69 148 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 148 220 4 17 37 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 148 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 148 220 2 33 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 220 (accept_3_3 65 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 220 4 16 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 220 (Polychromatic418967fa.accept_15_3_13_10_1_2332 63 148 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 220 2 31 74 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 220 4 15 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 220 (accept_3_3 59 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 220 2 29 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 220 (Polychromatic418967fa.accept_15_12_13_10_1_812 57 148 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 220 4 14 37 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 220
  (Polychromatic418967fa.accept_16_7_4_12_1_1806 55 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 220 2 27 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 220 (accept_3_3 53 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 220 4 13 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 148 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 220 2 25 74 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 220
  (Polychromatic418967fa.accept_15_4_13_10_1_1508 49 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 148 220 4 12 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 148 220 (accept_3_3 47 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 220 2 23 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 220 (Polychromatic418967fa.accept_13_6_5_12_1_307 45 148 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 220 4 11 37 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 220
  (Polychromatic418967fa.accept_13_4_5_12_1_751 43 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 220 2 21 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 220 (accept_3_3 41 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 220 4 10 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 148 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 220 2 19 74 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 220 4 9 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 220 (accept_3_3 35 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 220 2 17 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 148 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 220 4 8 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 220
  (Polychromatic418967fa.accept_15_1_13_10_1_1507 31 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 148 220 2 15 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 148 220 (accept_3_3 29 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 220 4 7 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 148 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 27 148 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 220 2 13 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25
  148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 220 4 6 37 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 220 (accept_3_3 23
  148 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 220 2 11 74 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 220
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 148 220 4 5 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 148 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 220 2 9 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 220 (accept_3_3 17 148 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 220 4 4 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 15 148
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 220 2 7 74 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 220
  (Polychromatic418967fa.accept_16_13_4_12_1_1805 13 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 220 4 3 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 220 (accept_3_3 11 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 220 2 5 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 220 4 2 37 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 220 (Polychromatic418967fa.accept_13_7_5_12_1_1305
  7 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 220 2 3 74 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 220 (accept_3_3 5
  148 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 220 4 1 37 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 220
  (Polychromatic418967fa.accept_15_3_13_10_1_2332 3 148 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 148 220 2 1 74 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 148 220 (Polychromatic418967fa.accept_13_1_5_12_1_306 1 148 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 148
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 147 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 220
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 147 220 (accept_3_3 71 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 147 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 147 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 220 (accept_3_3 68 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 66 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 220 (accept_3_3 65 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 220 (accept_3_3 62 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 220 (accept_3_3 59 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 147 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 58 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 220 (Polychromatic418967fa.accept_13_5_4_12_1_2058 57 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 220 (accept_3_3 56 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55
  147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 54 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 147 220 (accept_3_3 53 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 147 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 147 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 220 (accept_3_3 50 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 220
  (Polychromatic418967fa.accept_17_14_11_16_1_3261 48 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 220 (accept_3_3 47 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 147 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146 45 147
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 220 (accept_3_3 44 147
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 147 220 (accept_3_3 41 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 147 220 (Polychromatic418967fa.accept_16_8_3_12_1_1819 40 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 147 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 220 (accept_3_3 38 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 220
  (Polychromatic418967fa.accept_15_6_12_10_1_1543 36 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 220 (accept_3_3 35 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 147 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 220 (accept_3_3 32 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 220 (accept_3_3 29 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 220 (Polychromatic418967fa.accept_23_4_9_13_1_13067 27 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 220 (accept_3_3 26 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 220 (accept_3_3 23 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 220 (Polychromatic418967fa.accept_15_7_12_10_1_4335 22 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 220 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 220 (accept_3_3 20 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 220
  (Polychromatic418967fa.accept_12_6_3_4_1_394 18 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 220 (accept_3_3 17 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 220 (accept_3_3 14 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 220
  (Polychromatic418967fa.accept_17_12_11_16_1_6903 12 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 147 220 (accept_3_3 11 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 147 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 220 (Polychromatic418967fa.accept_15_9_12_10_1_809 9 147
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 220 (accept_3_3 8 147 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 220 (accept_3_3 5 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 220 (Polychromatic418967fa.accept_14_4_7_10_1_3888 4 147 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 220 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 220 (accept_3_3 2 147 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 146 220 (Eq.refl
  Bool.true) (allA_of_3_1 75 146 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 145 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 75 145 220 5 15 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 145 220 (accept_3_3 74 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 145 220 (Polychromatic418967fa.accept_27_19_10_4_1_13066 73 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 145 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 72
  145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 220 (accept_3_3 71
  145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 145 220 5 14 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 145 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 220 (accept_3_3 68 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 220 (Polychromatic418967fa.accept_19_10_12_11_1_7622 67 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 145 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 145 220 5 13 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 145 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 145 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 220 (accept_3_3 62 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 145 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 61 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 145 220 5 12 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 145 220 (accept_3_3 59 145 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 220 (accept_3_3 56 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  145 220 5 11 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 145 220 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 220 (accept_3_3 53 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 145 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 145 220 5 10 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 145 220 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 145 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 48 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 220 (accept_3_3 47 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 46 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 145 220 5 9 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 145 220 (accept_3_3 44 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 145 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 220 (accept_3_3 41 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 220 5 8 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 220 (accept_3_3 38 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 220 5 7 29 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 34 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 220 (accept_3_3 32 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 220 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 145 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 220 5 6 29 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 220 (accept_3_3 29 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 220
  (Polychromatic418967fa.accept_21_7_19_10_1_8567 28 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 220 (accept_3_3 26 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 145 220 5 5 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 145 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 220 (accept_3_3 23 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 220 (Polychromatic418967fa.accept_7_1_5_3_1_268
  22 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 145 220 5 4 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 145 220 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 220 (Polychromatic418967fa.accept_13_5_2_12_1_1301 18 145
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 220 (accept_3_3 17 145
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 145 220 5 3 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 145 220 (accept_3_3 14 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 13 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 220 (accept_3_3 11 145 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 145 220 5 2 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 145 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 220 (accept_3_3 8 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7
  145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 220
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 145 220 5 1 29 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 145 220 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 145 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 220 (accept_3_3 2 145 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  145 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 144 220 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 144 220 4 19 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 144 220 (Polychromatic418967fa.accept_17_7_8_16_1_6966 75 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 220 2 37 72 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 220
  (Polychromatic418967fa.accept_13_8_1_12_1_762 73 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 220 4 18 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 220 (accept_3_3 71 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 220 2 35 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 144 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 220 4 17 36 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 220
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 67 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 220 2 33 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 220 (accept_3_3 65 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 220 4 16 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 144 220 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 220 2 31 72 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 220
  (Polychromatic418967fa.accept_15_1_9_10_1_2327 61 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 220 4 15 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 220 (accept_3_3 59 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 220 2 29 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 144 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 144 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 220 4 14 36 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 220 2 27 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 220 (accept_3_3 53 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 220 4 13 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 220 (Polychromatic418967fa.accept_21_9_18_10_1_5388 51 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 220 2 25 72 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 220
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 49 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 220 4 12 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 220 (accept_3_3 47 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 220 2 23 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 220 (Polychromatic418967fa.accept_21_3_18_10_1_10020 45 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 220 4 11 36 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 220 2 21 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 220 (accept_3_3 41 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 220 4 10 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 220 (Polychromatic418967fa.accept_23_16_6_13_1_4665 39 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 220 2 19 72 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 220
  (Polychromatic418967fa.accept_13_11_1_12_1_742 37 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 220 4 9 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 220 (accept_3_3 35 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  144 220 2 17 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 144 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325 33 144 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 220 4 8 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 220 (Polychromatic418967fa.accept_13_5_1_12_1_740
  31 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 220 2 15 72 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 220
  (accept_3_3 29 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 220 4 7 36 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 220 2 13 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 220 (Polychromatic418967fa.accept_27_25_9_4_1_13065 25 144 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 220 4 6 36 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 220 (accept_3_3 23 144 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 220 2 11 72 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 220
  (Polychromatic418967fa.accept_13_8_1_12_1_762 21 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 220 4 5 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 220 (Polychromatic418967fa.accept_15_4_9_10_1_5384 19 144 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 220 2 9 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 220 (accept_3_3 17 144 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 220 4 4 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 220 2 7 72 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 220 4 3 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 220 (accept_3_3 11 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  144 220 2 5 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 220 (Polychromatic418967fa.accept_17_9_8_16_1_2176 9 144 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 220 4 2 36 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 220 (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 144 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 220 2 3 72 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 220 (accept_3_3 5
  144 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 220 4 1 36 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 220
  (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 144 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 144 220 2 1 72 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 143 220 (Eq.refl
  Bool.true) (allA_of_3_1 78 143 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 142 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 142 220 2 39 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 142 220 (accept_3_3 77 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 142 220 2 38 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 142 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 142 220 2 37 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 142 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 73 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 142 220 2 36 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 220 (accept_3_3 71 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 220 2 35 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 220 2 34 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 220 2 33 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 220 (accept_3_3 65 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 220 2 32 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 220 (Polychromatic418967fa.accept_15_3_7_10_1_2324 63 142 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 220 2 31 71 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 61 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 220 2 30 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 220 (accept_3_3 59 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 220 2 29 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 220 2 28 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 55 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 220 2 27 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 220 (accept_3_3 53 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 220 2 26 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 220 (Polychromatic418967fa.accept_9_6_7_4_1_212 51 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 220 2 25 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 49 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 220 2 24 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 220 (accept_3_3 47 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 220 2 23 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 220 (Polychromatic418967fa.accept_19_7_9_11_1_7493 45 142 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 220 2 22 71 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 220 2 21 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 220 (accept_3_3 41 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 220 2 20 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 39 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 220 2 19 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 220
  (Polychromatic418967fa.accept_9_1_7_4_1_52 37 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 220 2 18 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 220 (accept_3_3 35 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 220 2 17 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 220 2 16 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 220 2 15 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 220 (accept_3_3 29 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 220 2 14 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 220 2 13 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 220 2 12 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 220 (accept_3_3 23 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 220 2 11 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 220 2 10 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 220 2 9 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 220 (accept_3_3 17 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 220 2 8 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 220 2 7 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 220 2 6 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 220 (accept_3_3 11 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 220 2 5 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 220 (Polychromatic418967fa.accept_17_9_6_16_1_3280 9 142 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 220 2 4 71 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 220 2 3 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 220 (accept_3_3 5 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  220 2 2 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 220 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 142 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 220 2 1 71 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 142 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 141 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 220 (Polychromatic418967fa.accept_12_6_9_4_1_96
  78 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 220 (accept_3_3 77
  141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 220
  (Polychromatic418967fa.accept_15_1_6_10_1_23 76 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 141 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 75 141 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 220 (accept_3_3 74 141 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 220 (Polychromatic418967fa.accept_7_2_1_3_1_102
  72 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 220 (accept_3_3 71
  141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 70 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 141 220 (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 220 (accept_3_3 68 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 66 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 220 (accept_3_3 65 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 64 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 220 (Polychromatic418967fa.accept_15_3_6_10_1_1539 63 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 220 (accept_3_3 62 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 220 (accept_3_3 59 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 220 (accept_3_3 56 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 220 (accept_3_3 53 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 52 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 220 (accept_3_3 50 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 220
  (Polychromatic418967fa.accept_9_3_6_4_1_210 48 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 220 (accept_3_3 47 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 220 (Polychromatic418967fa.accept_17_11_5_16_1_5600 45 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 220 (accept_3_3 44 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 42 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 220 (accept_3_3 41 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 220 (accept_3_3 38 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 220
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 220 (accept_3_3 35 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 34 141 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 220 (accept_3_3 32 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31
  141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 220
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 220 (accept_3_3 29 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 28 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 220 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 220 (accept_3_3 26 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 220
  (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 220 (accept_3_3 23 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 220 (Polychromatic418967fa.accept_19_3_8_11_1_7609 22 141 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 220 (accept_3_3 20 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 220
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 220 (accept_3_3 17 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 220 (Polychromatic418967fa.accept_16_15_13_12_1_1787 15 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 220 (accept_3_3 14 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 220
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 220 (accept_3_3 11 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 10 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 220 (accept_3_3 8 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 220 (accept_3_3 5 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 220 (accept_3_3 2 141 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 140 220 (Eq.refl
  Bool.true) (allA_of_3_1 81 140 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 139 220 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 139 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 139 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 139 220 (accept_3_3 80 139 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 79 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 139 220
  (Polychromatic418967fa.accept_31_16_15_3_1_13064 78 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 139 220 (accept_3_3 77 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 139 220 (Polychromatic418967fa.accept_23_7_1_13_1_13063 76 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 75
  139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 220 (accept_3_3 74
  139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 139 220
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 139 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 220 (accept_3_3 71 139 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 139 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 70 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 220 (accept_3_3 68 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319 66 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 220 (accept_3_3 65 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 220 (Polychromatic418967fa.accept_17_13_3_16_1_5599 64 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 220 (accept_3_3 62 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 220 (Polychromatic418967fa.accept_18_7_13_4_1_1670 61 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 220 (accept_3_3 59 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 58 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 220 (accept_3_3 56 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 55 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 220 (Polychromatic418967fa.accept_15_9_4_10_1_2316 54 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 220 (accept_3_3 53 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 220 (Polychromatic418967fa.accept_15_7_4_10_1_1513 52 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 220 (accept_3_3 50 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 220 (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 220 (Polychromatic418967fa.accept_26_22_9_12_1_13062 48 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 220 (accept_3_3 47 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 139 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 220 (accept_3_3 44 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 43 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 220 (Polychromatic418967fa.accept_13_3_9_12_1_2062 42 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 220 (accept_3_3 41 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 220 (Polychromatic418967fa.accept_16_8_11_12_1_962 40 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 220 (accept_3_3 38 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 220 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 220 (accept_3_3 35 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 34 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 220 (accept_3_3 32 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 31 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 220 (accept_3_3 29 139 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 28 139 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 220 (accept_3_3 26 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 220 (Polychromatic418967fa.accept_15_9_4_10_1_2316 24 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 220 (accept_3_3 23 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 220 (accept_3_3 20 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 220 (Polychromatic418967fa.accept_25_19_14_20_1_13061 19 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 220 (accept_3_3 17 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 220 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 220 (accept_3_3 14 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 220 (Polychromatic418967fa.accept_15_13_4_10_1_821 13 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 220 (Polychromatic418967fa.accept_23_12_1_13_1_13060 12 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 220 (accept_3_3 11 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 139
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 220 (accept_3_3 8 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 220 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 220 (Polychromatic418967fa.accept_15_6_4_10_1_2319 6 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 220 (accept_3_3 5 139 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 220 (accept_3_3 2 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 220 (Polychromatic418967fa.accept_16_1_11_12_1_1774 1 139 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 138 220 (Eq.refl Bool.true) (allA_succ_of_gcd 82 138 220 2 41 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 220
  (Polychromatic418967fa.accept_12_9_6_4_1_402 81 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 220 2 40 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 138 220 2 39 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 138 220 (accept_3_3 77 138 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 220 2 38 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 220 (Polychromatic418967fa.accept_12_3_6_4_1_400
  75 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 220 2 37 69 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 73 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 220 2 36 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 220 (accept_3_3 71 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 220 2 35 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 69 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 220 2 34 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 220
  (Polychromatic418967fa.accept_15_7_3_10_1_817 67 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 220 2 33 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 220 (accept_3_3 65 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 220 2 32 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 220 2 31 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 61 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 220 2 30 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 220 (accept_3_3 59 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 220 2 29 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 220 2 28 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 55 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 220 2 27 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 220 (accept_3_3 53 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 220 2 26 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 220 2 25 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 220
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 49 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 138 220 2 24 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 138 220 (accept_3_3 47 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 220 2 23 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 220 2 22 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 220
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 220 2 21 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 220 (accept_3_3 41 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 220 2 20 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 220 2 19 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 220
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 220 2 18 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 220 (accept_3_3 35 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 220 2 17 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 220 2 16 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 220
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 31 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 220 2 15 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 220 (accept_3_3 29 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 220 2 14 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 220 2 13 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 220 2 12 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 220 (accept_3_3 23 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 220 2 11 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 220 2 10 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 220
  (Polychromatic418967fa.accept_9_1_3_4_1_47 19 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 220 2 9 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 220 (accept_3_3 17 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 220 2 8 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 220 2 7 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 220
  (Polychromatic418967fa.accept_15_13_3_10_1_2296 13 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 138 220 2 6 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 138 220 (accept_3_3 11 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 220 2 5 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 220 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 220 2 4 69 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 220
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 220 2 3 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 220 (accept_3_3 5 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  220 2 2 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 138 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 220 2 1 69 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 220 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 138 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 137 220 (Eq.refl
  Bool.true) (allA_of_3_1 84 137 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 136 220 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 136 220 4 21 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 136 220 (accept_3_3 83 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 136 220 2 41 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 136 220 (Polychromatic418967fa.accept_15_6_1_10_1_1549 81 136 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 136 220 4 20 34 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 136 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 79 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 136 220 2 39 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 220 (accept_3_3 77 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 220 4 19 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 75 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 220 2 37 68 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 220
  (Polychromatic418967fa.accept_15_13_1_10_1_816 73 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 220 4 18 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 136 220 (accept_3_3 71 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 220 2 35 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 69 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 220 4 17 34 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 220
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 67 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 220 2 33 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 220 (accept_3_3 65 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 220 4 16 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 220 (Polychromatic418967fa.accept_16_15_8_12_1_2737 63 136 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 220 2 31 68 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 61 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 220 4 15 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 220 (accept_3_3 59 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 220 2 29 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 57 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 220 4 14 34 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 220
  (Polychromatic418967fa.accept_16_7_8_12_1_4902 55 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 220 2 27 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 220 (accept_3_3 53 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 220 4 13 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 51 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 220 2 25 68 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 220
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 49 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 136 220 4 12 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 136 220 (accept_3_3 47 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 220 2 23 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 220 (Polychromatic418967fa.accept_16_13_8_12_1_2723 45 136 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 220 4 11 34 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 220
  (Polychromatic418967fa.accept_9_7_1_4_1_217 43 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 220 2 21 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 220 (accept_3_3 41 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 220 4 10 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 39 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 220 2 19 68 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 220
  (Polychromatic418967fa.accept_15_7_1_10_1_305 37 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 220 4 9 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 136 220 (accept_3_3 35 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  136 220 2 17 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 136 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 33 136 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 220 4 8 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 220 (Polychromatic418967fa.accept_13_5_6_12_1_2750
  31 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 220 2 15 68 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 220
  (accept_3_3 29 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 220 4 7 34 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 220
  (Polychromatic418967fa.accept_16_11_8_12_1_1767 27 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 136 220 2 13 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 136 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 25 136 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 136 220 4 6 34 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 136 220 (accept_3_3 23 136 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 136 220 2 11 68 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 136 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 21 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 136 220 4 5 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 136 220 (Polychromatic418967fa.accept_16_3_8_12_1_2736 19 136 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 220 2 9 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 220 (accept_3_3 17 136 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 220 4 4 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 136 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 220 2 7 68 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 220
  (Polychromatic418967fa.accept_15_13_1_10_1_816 13 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 220 4 3 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 136 220 (accept_3_3 11 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  136 220 2 5 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 136 220 (Polychromatic418967fa.accept_15_9_1_10_1_4316 9 136 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 220 4 2 34 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 136 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 220 2 3 68 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 220 (accept_3_3 5
  136 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136 220 4 1 34 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 136 220
  (Polychromatic418967fa.accept_9_3_1_4_1_216 3 136 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 136 220 2 1 68 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 136 220 (Polychromatic418967fa.accept_16_1_8_12_1_405 1 136 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 136
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 135 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 135 220 5 17 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 135 220 (Polychromatic418967fa.accept_13_6_5_12_1_307 84 135
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 220 (accept_3_3 83 135
  220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 82 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 135 220 (Polychromatic418967fa.accept_21_18_9_10_1_2571 81 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 135 220 5 16 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 135 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 220 (accept_3_3 77 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 135 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 76 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 135 220 5 15 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 135 220 (accept_3_3 74 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 135 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 220
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 220 (accept_3_3 71 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  135 220 5 14 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 135 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 220 (accept_3_3 68 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 220 (Polychromatic418967fa.accept_12_6_3_4_1_394
  66 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 135 220 5 13 27 44
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 135 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 64 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 135 220 (Polychromatic418967fa.accept_28_7_23_24_1_13059 63 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 220 (accept_3_3 62 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 220 5 12 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 220 (accept_3_3 59 135 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 220 (Polychromatic418967fa.accept_13_6_5_12_1_307
  58 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 220
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 220 (accept_3_3 56 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  135 220 5 11 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 135 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 220 (accept_3_3 53 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 135 220 (Polychromatic418967fa.accept_16_4_7_12_1_2734 52 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 220
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 135 220 5 10 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 220 (Polychromatic418967fa.accept_7_6_2_3_1_107
  48 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 220 (accept_3_3 47
  135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 220
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 46 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 135 220 5 9 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 135 220 (accept_3_3 44 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 42 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 220 (accept_3_3 41 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 220 5 8 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 135 220
  (Polychromatic418967fa.accept_21_18_9_10_1_2571 39 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 220 (accept_3_3 38 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 135 220 5 7 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 220 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 220 (accept_3_3 32 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 220 5 6 27 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 220 (accept_3_3 29 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 220 (Polychromatic418967fa.accept_13_2_5_12_1_2043 28 135
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 220
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 220 (accept_3_3 26 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  135 220 5 5 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 135 220 (Polychromatic418967fa.accept_16_8_7_12_1_7207 24 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 220 (accept_3_3 23 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 220 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 220 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 135
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 220 5 4 27 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 220
  (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 135 220 (Polychromatic418967fa.accept_12_6_3_4_1_394 18 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 220 (accept_3_3 17 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 135 220 (Polychromatic418967fa.accept_19_16_2_11_1_4705 16 135 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 220 5 3 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 220 (accept_3_3 14 135 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13
  135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 220
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 220 (accept_3_3 11 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  135 220 5 2 27 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 135 220 (Polychromatic418967fa.accept_19_9_2_11_1_7581 9 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 220 (accept_3_3 8 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 220 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 220 5 1 27 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 220
  (Polychromatic418967fa.accept_13_4_5_12_1_751 4 135 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 135 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 220 (accept_3_3 2 135 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 135 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 135 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 134 220
  (Eq.refl Bool.true) (allA_of_3_1 87 134 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 133 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 133 220 (accept_3_3 86 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 133 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 85 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 133 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 84 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 133 220 (accept_3_3 83 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 82 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 220 (accept_3_3 80 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 133 220 (Polychromatic418967fa.accept_15_4_13_10_1_1508 79 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 78 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 133 220 (accept_3_3 77 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 133 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 76 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 220 (accept_3_3 74 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 73 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 220
  (Polychromatic418967fa.accept_15_12_13_10_1_812 72 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 133 220 (accept_3_3 71 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 133 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 70 133 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 220 (accept_3_3 68 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 220 (Polychromatic418967fa.accept_13_2_3_12_1_735
  67 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 66 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 220 (accept_3_3 65 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 64 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 220 (accept_3_3 62 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 220 (Polychromatic418967fa.accept_13_9_3_12_1_2025 61 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 60 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 220 (accept_3_3 59 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 58 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 220 (accept_3_3 56 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 55 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 220
  (Polychromatic418967fa.accept_13_2_3_12_1_735 54 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 220 (accept_3_3 53 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 220 (Polychromatic418967fa.accept_16_4_5_12_1_2749 52 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 220 (accept_3_3 50 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 49 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 48 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 220 (accept_3_3 47 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 46 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 220 (accept_3_3 44 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 220 (Polychromatic418967fa.accept_13_4_3_12_1_2066 43 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 42 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 220 (accept_3_3 41 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 220 (Polychromatic418967fa.accept_16_8_5_12_1_3812 40 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 220 (accept_3_3 38 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 220
  (Polychromatic418967fa.accept_16_4_5_12_1_2749 36 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 220 (accept_3_3 35 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 34 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 220 (accept_3_3 32 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 220 (Polychromatic418967fa.accept_14_3_7_10_1_2146 31 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 220 (accept_3_3 29 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 220 (accept_3_3 26 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 25 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 133 220 (accept_3_3 23 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 133 220 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 220 (accept_3_3 20 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 19 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 133 220
  (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 220 (accept_3_3 17 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 220 (Polychromatic418967fa.accept_15_1_13_10_1_1507 16 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 220 (accept_3_3 14 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 220 (Polychromatic418967fa.accept_18_13_7_4_1_2738 13 133 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 220
  (Polychromatic418967fa.accept_9_3_7_4_1_53 12 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 220 (accept_3_3 11 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 220 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 220 (accept_3_3 8 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 220 (Polychromatic418967fa.accept_16_7_5_12_1_4824 7 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 220
  (Polychromatic418967fa.accept_9_6_7_4_1_212 6 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 220 (accept_3_3 5 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 220 (Polychromatic418967fa.accept_13_4_3_12_1_2066 4 133 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 220 (accept_3_3 2 133 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 220 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 133 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 132 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 132 220 44 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 132 220 (Polychromatic418967fa.accept_14_3_6_10_1_752 87 132 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 132 220 2 43 66 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 132 220
  (Polychromatic418967fa.accept_16_5_4_12_1_3800 85 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 220 4 21 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 220 (accept_3_3 83 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 132 220 2 41 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 132 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 220 4 20 33 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 220 2 39 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 132 220 11 7 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 76 132 220 4 19 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 75 132 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 220 2 37 66 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 73 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 220 4 18 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 220 (accept_3_3 71 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 220 2 35 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 220 (Polychromatic418967fa.accept_13_4_2_12_1_2800 69 132 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 220 4 17 33 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 67 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 220 22 3 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 132 220 (accept_3_3 65 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64
  132 220 4 16 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 132 220 (Polychromatic418967fa.accept_16_15_4_12_1_2731 63 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 220 2 31 66 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 220
  (Polychromatic418967fa.accept_9_7_6_4_1_483 61 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 220 4 15 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 220 (accept_3_3 59 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 220 2 29 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 57 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 220 4 14 33 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 132 220 11 5 12 20 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 132 220 2 27 66 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 220 (accept_3_3 53
  132 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 220 4 13 33 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 220 2 25 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 220 (Polychromatic418967fa.accept_13_10_2_12_1_1332 49 132 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 220 4 12 33 55 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 220 (accept_3_3 47 132 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 220 2 23 66 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 220
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 220 44 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 132 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 43 132 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 220 2 21 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 220 (accept_3_3 41 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 220 4 10 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 220 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 220 2 19 66 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 220 4 9 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 220 (accept_3_3 35 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  132 220 2 17 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  33 132 220 11 3 12 20 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 132 220 4 8 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 132 220 (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 132 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 220 2 15 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 220 (accept_3_3 29 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 220 4 7 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 220 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 132
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 220 2 13 66 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 220
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 220 4 6 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 220 (accept_3_3 23 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  132 220 22 1 6 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  21 132 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 132 220 4 5 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 132 220 (Polychromatic418967fa.accept_9_1_6_4_1_49 19 132 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 220 2 9 66 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 220 (accept_3_3 17 132 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 220 4 4 33 55 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 220
  (Polychromatic418967fa.accept_16_15_4_12_1_2731 15 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 220 2 7 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 220 (Polychromatic418967fa.accept_15_13_12_10_1_4352 13 132 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 220 4 3 33 55 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 220 11 1 12 20
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 220 2 5 66
  110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 220
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 220 4 2 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 220 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 132 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 220 2 3 66 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 220 (accept_3_3 5 132 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 220 4 1 33 55 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 220 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 132 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 220 2 1 66 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 220
  (Polychromatic418967fa.accept_9_1_6_4_1_49 1 132 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  90 131 220 (Eq.refl Bool.true) (allA_of_3_1 90 131 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 91 130 220
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 130 220 10 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 130 220 (accept_3_3 89 130 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 130 220 2 44 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 130 220 (Polychromatic418967fa.accept_16_7_2_12_1_1754 87 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 130 220 2 43 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 85 130 220 5 17 26 44 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 130 220 2 42 65 110
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 130 220
  (accept_3_3 83 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 130 220 2 41 65 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 130 220
  (Polychromatic418967fa.accept_16_1_2_12_1_1757 81 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 130 220 10 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 130 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 79 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 130 220 2 39 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 130 220 (accept_3_3 77 130 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 130 220 2 38 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 130 220 5 15 26 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 130 220 2 37 65 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 73 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 220 2 36 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 220 (accept_3_3 71 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 220 10 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 130 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 220 2 34 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 67 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 220 2 33 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 130 220 5 13 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 64 130 220 2 32 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 220 (Polychromatic418967fa.accept_14_7_4_10_1_1351 63 130
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 220 2 31 65 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 61 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 220 10 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 220 (accept_3_3 59 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 220 2 29 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 130 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 220 2 28 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 130 220 5 11 26 44 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 130 220 2 27 65 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 220 (accept_3_3 53
  130 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 130 220 2 26 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 130 220
  (Polychromatic418967fa.accept_19_13_16_11_1_6047 51 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 130 220 10 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 130 220 (Polychromatic418967fa.accept_12_1_10_4_1_380 49 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 130 220 2 24 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 130 220 (accept_3_3 47 130 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 130 220 2 23 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 130 220 5 9 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 130 220 2 22 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 220
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 220 2 21 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 220 (accept_3_3 41 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 220 10 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 220 (Polychromatic418967fa.accept_16_7_2_12_1_1754 39 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 220 2 19 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 220
  (Polychromatic418967fa.accept_12_1_10_4_1_380 37 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 220 2 18 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 130 220 5 7 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 130 220 2 17 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 130 220 (Polychromatic418967fa.accept_16_1_2_12_1_1757 33 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 220 2 16 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 31 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 220 10 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 220 (accept_3_3 29 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 220 2 14 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 220 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 130 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 220 2 13 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 130 220 5 5 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 130 220 2 12 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 130 220 (accept_3_3 23 130 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 130 220 2 11 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 130 220
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 130 220 10 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 130 220 (Polychromatic418967fa.accept_12_7_10_4_1_382 19 130 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 130 220 2 9 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 130 220 (accept_3_3 17 130 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 130 220 2 8 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 130 220 5 3 26 44 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 130 220 2 7 65 110 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 220
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 130 220 2 6 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 130 220 (accept_3_3 11 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 220 10 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 220 (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 130 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 220 2 4 65 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 220
  (Polychromatic418967fa.accept_12_7_10_4_1_382 7 130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 220 2 3 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 130 220 5 1 26 44 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 130 220 2 2 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 130 220 (Polychromatic418967fa.accept_25_3_5_20_1_13058 3 130 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 220 2 1 65 110 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 220 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  130 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  220))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 129 220
  (Eq.refl Bool.true) (allA_succ_of_accept 91 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 91 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 90 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 89 129 220 (accept_3_3 89 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  88 129 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 88 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 129 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 87 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 220 (accept_3_3 86 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 220
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 84 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 220 (accept_3_3 83 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 82 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 220 (Polychromatic418967fa.accept_19_5_15_11_1_7568 81 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 220 (accept_3_3 80 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 78 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 220 (accept_3_3 77 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 220 (Polychromatic418967fa.accept_14_6_3_10_1_3905 76 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 220 (Polychromatic418967fa.accept_16_11_1_12_1_1795 75 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 220 (accept_3_3 74 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 72 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 220 (accept_3_3 71 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 70 129 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 69 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 220 (accept_3_3 68 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 67
  129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 66 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 220 (accept_3_3 65 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 64 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 220 (Polychromatic418967fa.accept_14_7_3_10_1_1364 63 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 220 (accept_3_3 62 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 60 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 220 (accept_3_3 59 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 220 (Polychromatic418967fa.accept_17_7_10_16_1_5582 58 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 220 (Polychromatic418967fa.accept_15_12_9_10_1_2326 57 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 220 (accept_3_3 56 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 54 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 220 (accept_3_3 53 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 52 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 51 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 220 (accept_3_3 50 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 220
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 220 (accept_3_3 47 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 46 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 220 (accept_3_3 44 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 42 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 220 (accept_3_3 41 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 220 (Polychromatic418967fa.accept_16_8_1_12_1_984 40 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 220 (Polychromatic418967fa.accept_19_1_15_11_1_4712 39 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 220 (accept_3_3 38 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 220
  (Polychromatic418967fa.accept_16_4_1_12_1_1792 36 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 220 (accept_3_3 35 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 220 (accept_3_3 32 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 220 (accept_3_3 29 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 220 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 220 (accept_3_3 26 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 220 (accept_3_3 23 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 220 (Polychromatic418967fa.accept_21_1_3_10_1_5401 22 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 220 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 220 (accept_3_3 20 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 220
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 220 (accept_3_3 17 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 220 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 129 220 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 220 (accept_3_3 14 129 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 220
  (Polychromatic418967fa.accept_15_12_9_10_1_2326 12 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 220 (accept_3_3 11 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 220 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 129 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 220 (Polychromatic418967fa.accept_17_9_10_16_1_3217 9 129
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 220 (accept_3_3 8 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 220
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 220 (accept_3_3 5 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 220 (Polychromatic418967fa.accept_15_4_9_10_1_5384 4 129 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 220 (Polychromatic418967fa.accept_15_3_9_10_1_2325 3 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 220 (accept_3_3 2 129 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 220 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 128 220
  (Eq.refl Bool.true) (allA_of_3_1 93 128 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 127 220 (Eq.refl
  Bool.true) (allA_succ_of_accept 93 127 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 93 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 127 220 (accept_3_3 92 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 91 127 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 91 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 127 220
  (Polychromatic418967fa.accept_25_15_2_20_1_13057 90 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 127 220 (accept_3_3 89 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 88 127 220 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 127 220 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 220 (accept_3_3 86 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 220
  (Polychromatic418967fa.accept_13_7_10_12_1_2047 85 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 127 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 84 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 127 220 (accept_3_3 83 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 82 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 82 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 81 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 127 220 (accept_3_3 80 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 127 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 78 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 127 220 (accept_3_3 77 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 127 220 (Polychromatic418967fa.accept_13_11_10_12_1_1338 76 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 127 220 (accept_3_3 74 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 127 220 (Polychromatic418967fa.accept_13_8_10_12_1_1337 73 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 127 220 (accept_3_3 71 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 127 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 70 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 69 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 127 220 (accept_3_3 68 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 67 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 127 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 66 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 220 (accept_3_3 65 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 220 (Polychromatic418967fa.accept_15_4_7_10_1_807 64 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 127 220 (accept_3_3 62 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 220 (accept_3_3 59 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 57 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 127 220 (accept_3_3 56 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 127 220 (Polychromatic418967fa.accept_19_17_13_11_1_2222 55 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 127 220 (accept_3_3 53 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 127 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 52 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 127 220 (accept_3_3 50 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 127 220 (Polychromatic418967fa.accept_15_4_7_10_1_807 49 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 127 220 (Polychromatic418967fa.accept_9_3_1_4_1_216 48 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 127 220 (accept_3_3 47 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 220 (accept_3_3 44 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 220 (Polychromatic418967fa.accept_8_3_7_4_1_42 43 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 42 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 220 (accept_3_3 41 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 127 220 (accept_3_3 38 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 127 220 (Polychromatic418967fa.accept_16_4_15_12_1_1745 36 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 220 (accept_3_3 35 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 127 220 (accept_3_3 32 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 127 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 31 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 220 (accept_3_3 29 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 220 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 127 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 220 (accept_3_3 26 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 24 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 220 (accept_3_3 23 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 220 (accept_3_3 20 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 220 (accept_3_3 17 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 220 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 220 (accept_3_3 14 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 220 (Polychromatic418967fa.accept_16_13_15_12_1_1748 13 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 220 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 220 (accept_3_3 11 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 220 (Polychromatic418967fa.accept_12_10_7_4_1_820 10 127
  220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 220 (accept_3_3 8 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 220 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 220 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 220 (accept_3_3 5 127 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 220 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 220
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 220 (accept_3_3 2 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 220 (Polychromatic418967fa.accept_15_1_7_10_1_287 1 127 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 126
  220 (Eq.refl Bool.true) (allA_succ_of_gcd 94 126 220 2 47 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 93 126 220
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 126 220 2 46 63 110 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 126 220
  (Polychromatic418967fa.accept_15_1_6_10_1_23 91 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 220 2 45 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 220 (accept_3_3 89 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 126 220 2 44 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 87 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 126 220 2 43 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 126 220
  (Polychromatic418967fa.accept_25_10_1_20_1_13056 85 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 84 126 220 2 42 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 126 220 (accept_3_3 83 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 126 220 2 41 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 81 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 126 220 2 40 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 126 220
  (Polychromatic418967fa.accept_15_4_6_10_1_823 79 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 220 2 39 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 220 (accept_3_3 77 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 126 220 2 38 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 75 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 126 220 2 37 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 126 220
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 73 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 220 2 36 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 220 (accept_3_3 71 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 126 220 2 35 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 69 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 126 220 2 34 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 220
  (Polychromatic418967fa.accept_19_10_12_11_1_7622 67 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 126 220 2 33 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 126 220 (accept_3_3 65 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 126 220 2 32 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 63 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 126 220 2 31 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 220
  (Polychromatic418967fa.accept_15_1_6_10_1_23 61 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 220 2 30 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 220 (accept_3_3 59 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 126 220 2 29 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 57 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 126 220 2 28 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 220
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 55 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 220 2 27 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 220 (accept_3_3 53 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 126 220 2 26 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 51 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 126 220 2 25 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 220
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 49 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 220 2 24 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 220 (accept_3_3 47 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 220 2 23 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 45 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 126 220 2 22 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 220
  (Polychromatic418967fa.accept_19_5_12_11_1_10460 43 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 126 220 2 21 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 126 220 (accept_3_3 41 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 220 2 20 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 39 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 126 220 2 19 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 220
  (Polychromatic418967fa.accept_17_3_7_16_1_3251 37 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 220 2 18 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 220 (accept_3_3 35 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 220 2 17 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 33 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 220 2 16 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 220
  (Polychromatic418967fa.accept_15_1_6_10_1_23 31 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 220 2 15 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 220 (accept_3_3 29 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 220 2 14 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 27 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 126 220 2 13 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 220
  (Polychromatic418967fa.accept_17_8_7_16_1_9508 25 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 220 2 12 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 220 (accept_3_3 23 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 126 220 2 11 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 126 220 2 10 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 220
  (Polychromatic418967fa.accept_15_4_6_10_1_823 19 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 220 2 9 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 220 (accept_3_3 17 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 220 2 8 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 220 2 7 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 220
  (Polychromatic418967fa.accept_19_13_12_11_1_1249 13 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 220 2 6 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 220 (accept_3_3 11 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 220 2 5 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 126 220 (Polychromatic418967fa.accept_12_9_6_4_1_402 9 126 220 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 220 2 4 63 110 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 220
  (Polychromatic418967fa.accept_19_7_12_11_1_7621 7 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 220 2 3 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 220 (accept_3_3 5 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126
  220 2 2 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  126 220 (Polychromatic418967fa.accept_12_3_6_4_1_400 3 126 220 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 126 220 2 1 63 110 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 126 220 (Polychromatic418967fa.accept_15_1_6_10_1_23 1 126 220 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  220)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_220_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


