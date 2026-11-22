-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch184
-- name    : Polychromatic418967fa_Branch184
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:05.213653+00:00
-- url     : https://prove2.me/theorems/33e4309b-85d2-43b5-b276-287c32f79313
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch184_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_184 : allB 184 184 :=
  allB_succ' 2 183 184 (Eq.refl Bool.true) (allA_succ_of_accept 1 183 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  183 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 184)) (allB_succ' 3 182 184
  (Eq.refl Bool.true) (allA_of_3_1 3 182 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 181 184 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 181 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 181 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 184 (accept_3_3 2 181 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 184)))) (allB_succ' 5 180 184 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 180 184 4 1 45 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 180 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 184 2 1 90 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 184 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 180 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 184))))) (allB_succ' 6 179 184 (Eq.refl
  Bool.true) (allA_of_3_1 6 179 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 178 184 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 178 184 2 3 89 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 184 (accept_3_3 5 178 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  184 2 2 89 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 184 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 178 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 184 2 1 89 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 178 184 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 178 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 184))))))) (allB_succ' 8 177 184 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 177 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 177 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 184 (Polychromatic418967fa.accept_12_6_9_4_1_96 6 177 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 184 (accept_3_3 5 177 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 184 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  4 177 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 184
  (Polychromatic418967fa.accept_9_3_6_4_1_210 3 177 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 177 184 (accept_3_3 2 177 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  177 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 177 184)))))))) (allB_succ' 9 176 184 (Eq.refl Bool.true) (allA_of_3_1 9 176 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 175 184 (Eq.refl Bool.true) (allA_succ_of_accept 9 175 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 184 (accept_3_3 8 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 184 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 184 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 175 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 184 (accept_3_3 5 175 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 184 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 175 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 184 (accept_3_3 2 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 184 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 175 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 184)))))))))) (allB_succ' 11 174 184 (Eq.refl Bool.true) (allA_succ_of_gcd 10 174 184 2 5 87
  92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 184
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 174 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 184 2 4 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 184 (Polychromatic418967fa.accept_9_7_3_4_1_218 7 174 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 184 2 3 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 184 (accept_3_3 5 174 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 184 2 2 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 174 184 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 174 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 184 2 1 87 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  174 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 184))))))))))) (allB_succ' 12 173
  184 (Eq.refl Bool.true) (allA_of_3_1 12 173 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 172 184
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 172 184 4 3 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 172 184 (accept_3_3 11 172 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 184 2 5 86 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 172 184 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 172 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 184 4 2 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 172 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 184 2 3 86 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 184 (accept_3_3 5 172 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172 184 4 1 43 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 172 184 (Polychromatic418967fa.accept_9_3_1_4_1_216 3
  172 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 184 2 1 86 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 184
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 172 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 184))))))))))))) (allB_succ' 14 171 184 (Eq.refl Bool.true) (allA_succ_of_accept 13 171 184
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 171 184 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 184 (accept_3_3 11 171 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 184 (Polychromatic418967fa.accept_15_10_6_4_1_1256 10 171 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 184
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 184 (accept_3_3 8 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 184 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 171 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 184 (accept_3_3 5 171 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 184 (Polychromatic418967fa.accept_16_4_11_8_1_1574 4 171 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 184
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 184 (accept_3_3 2 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 171 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 184)))))))))))))) (allB_succ' 15 170 184 (Eq.refl Bool.true) (allA_of_3_1 15 170 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 169 184 (Eq.refl Bool.true) (allA_succ_of_accept 15 169 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 184 (accept_3_3 14 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 184 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 184 (Polychromatic418967fa.accept_9_3_7_4_1_53 12 169 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 184 (accept_3_3 11 169 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 184 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 169 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 184 (accept_3_3 8 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 184 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 184 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 184 (accept_3_3 5 169 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 184 (Polychromatic418967fa.accept_16_4_9_8_1_2509 4 169 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 184 (accept_3_3 2 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 169 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 184)))))))))))))))) (allB_succ' 17 168 184 (Eq.refl Bool.true) (allA_succ_of_gcd 16 168 184
  8 2 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168
  184 (Polychromatic418967fa.accept_18_15_6_4_1_5147 15 168 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 184 2 7 84 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 184 (Polychromatic418967fa.accept_25_13_18_9_1_10603 13 168 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 184 4 3 42 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 184 (accept_3_3 11
  168 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 184 2 5 84 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 184
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 168 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 184 8 1 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 184 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 168 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 184 2 3 84 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 184 (accept_3_3 5 168 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 184 4 1 42 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 184 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 168 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 184 2 1 84 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 184 (Polychromatic418967fa.accept_9_1_6_4_1_49 1
  168 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 184))))))))))))))))) (allB_succ' 18
  167 184 (Eq.refl Bool.true) (allA_of_3_1 18 167 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 166 184
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 166 184 2 9 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 166 184 (accept_3_3 17 166 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 184 2 8 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 166 184 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 166 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 184 2 7 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 184 (Polychromatic418967fa.accept_12_1_10_4_1_380
  13 166 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 184 2 6 83 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 184
  (accept_3_3 11 166 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 184 2 5 83 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 184
  (Polychromatic418967fa.accept_24_9_22_16_1_826 9 166 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 184 2 4 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 184 (Polychromatic418967fa.accept_12_7_10_4_1_382 7 166 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 184 2 3 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 184 (accept_3_3 5 166 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 184 2 2 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 166 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 184 2 1 83 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 184 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  166 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 184))))))))))))))))))) (allB_succ'
  20 165 184 (Eq.refl Bool.true) (allA_succ_of_accept 19 165 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 165 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 184
  (Polychromatic418967fa.accept_12_6_9_4_1_96 18 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 184 (accept_3_3 17 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 184 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 184 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 184 (accept_3_3 14 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 184
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 184 (accept_3_3 11 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 184 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 184 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 184 (accept_3_3 8 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 165 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 184
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 184 (accept_3_3 5 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 184 (Polychromatic418967fa.accept_16_4_5_8_1_2425 4 165 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 184 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 184 (accept_3_3 2 165 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 184)))))))))))))))))))) (allB_succ' 21 164 184
  (Eq.refl Bool.true) (allA_of_3_1 21 164 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 163 184 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 163 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 184 (accept_3_3 20 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 184 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 163 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 184
  (Polychromatic418967fa.accept_13_5_7_2_1_852 18 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 184 (accept_3_3 17 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 184 (accept_3_3 14 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 184 (Polychromatic418967fa.accept_16_13_3_8_1_2422 13 163 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 184
  (Polychromatic418967fa.accept_9_3_1_4_1_216 12 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 184 (accept_3_3 11 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 184 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 184 (accept_3_3 8 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 163 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 184
  (Polychromatic418967fa.accept_9_6_1_4_1_474 6 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 184 (accept_3_3 5 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 184 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 163 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 184 (accept_3_3 2 163 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 184 (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 163 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 184)))))))))))))))))))))) (allB_succ' 23 162 184
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 162 184 2 11 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 184 (Polychromatic418967fa.accept_12_9_6_4_1_402 21 162 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 184 2 10 81 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 184
  (Polychromatic418967fa.accept_20_19_2_4_1_2057 19 162 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 184 2 9 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 184 (accept_3_3 17 162 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  162 184 2 8 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 162 184 (Polychromatic418967fa.accept_12_3_6_4_1_400 15 162 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 162 184 2 7 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 162 184 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 162 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 184 2 6 81 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 184 (accept_3_3 11 162 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 184 2 5 81 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 184
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 162 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 184 2 4 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 184 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 162 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 184 2 3 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 184 (accept_3_3 5 162 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 184 2 2 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 162 184 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 184 2 1 81 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 184 (Polychromatic418967fa.accept_13_1_6_2_1_377 1
  162 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 184)))))))))))))))))))))))
  (allB_succ' 24 161 184 (Eq.refl Bool.true) (allA_of_3_1 24 161 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 25 160 184 (Eq.refl Bool.true) (allA_succ_of_gcd 24 160 184 8 3 20 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 184 (accept_3_3 23 160 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 184 2 11 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 184 (Polychromatic418967fa.accept_9_3_7_4_1_53 21
  160 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 184 4 5 40 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 184
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 160 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 184 2 9 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 160 184 (accept_3_3 17 160 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  160 184 8 2 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 160 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 160 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 160 184 2 7 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 160 184 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 160 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 160 184 4 3 40 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 160 184 (accept_3_3 11
  160 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 184 2 5 80 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 184
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 160 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 160 184 8 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 160 184 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 160 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 184 2 3 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 184 (accept_3_3 5 160 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 160 184 4 1 40 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 160 184 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 160 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 184 2 1 80 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  160 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 184)))))))))))))))))))))))))
  (allB_succ' 26 159 184 (Eq.refl Bool.true) (allA_succ_of_accept 25 159 184 (Polychromatic418967fa.accept_6_1_3_4_1_1
  25 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 184
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 159 184 (accept_3_3 23 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 159 184 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 159 184 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 184 (accept_3_3 20 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 159 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 184
  (Polychromatic418967fa.accept_7_4_5_2_1_243 18 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 184 (accept_3_3 17 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 184 (Polychromatic418967fa.accept_9_7_6_4_1_483 16 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 184 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 159 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 184 (accept_3_3 14 159 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 159 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 184
  (Polychromatic418967fa.accept_9_3_6_4_1_210 12 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 184 (accept_3_3 11 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 184 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 184 (accept_3_3 8 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 184
  (Polychromatic418967fa.accept_12_6_3_4_1_394 6 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 184 (accept_3_3 5 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 184 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 184 (accept_3_3 2 159 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 159 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 184)))))))))))))))))))))))))) (allB_succ' 27 158 184
  (Eq.refl Bool.true) (allA_of_3_1 27 158 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 157 184 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 157 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 184 (accept_3_3 26 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 184 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 157 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 184
  (Polychromatic418967fa.accept_17_7_4_14_1_2106 24 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 184 (accept_3_3 23 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 184 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 184 (accept_3_3 20 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 184 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 157 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 184
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 184 (accept_3_3 17 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 184 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 184 (accept_3_3 14 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 184 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 184
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 184 (accept_3_3 11 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 184 (Polychromatic418967fa.accept_12_10_1_4_1_392 10 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 184 (accept_3_3 8 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 184 (Polychromatic418967fa.accept_17_7_4_14_1_2106 7 157 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 184
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 184 (accept_3_3 5 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 184 (Polychromatic418967fa.accept_16_4_13_8_1_3424 4 157 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 184 (accept_3_3 2 157 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 184 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 184)))))))))))))))))))))))))))) (allB_succ' 29 156
  184 (Eq.refl Bool.true) (allA_succ_of_gcd 28 156 184 4 7 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 184 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 156 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 184 2 13 78 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 184
  (Polychromatic418967fa.accept_9_7_3_4_1_218 25 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 184 4 6 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 184 (accept_3_3 23 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  156 184 2 11 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 156 184 (Polychromatic418967fa.accept_16_5_12_8_1_2521 21 156 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 184 4 5 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 184 (Polychromatic418967fa.accept_9_1_3_4_1_47 19
  156 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 184 2 9 78 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 184 (accept_3_3 17
  156 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 184 4 4 39 46 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 184
  (Polychromatic418967fa.accept_9_6_3_4_1_477 15 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 184 2 7 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 156 184 (Polychromatic418967fa.accept_15_13_6_4_1_1221 13 156 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 184 4 3 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 184 (accept_3_3 11 156 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 184 2 5 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 184 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 156 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 184 4 2 39 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 184
  (Polychromatic418967fa.accept_9_7_3_4_1_218 7 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 184 2 3 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 184 (accept_3_3 5 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156
  184 4 1 39 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  156 184 (Polychromatic418967fa.accept_16_3_12_8_1_808 3 156 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 156 184 2 1 78 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 156 184 (Polychromatic418967fa.accept_9_1_3_4_1_47 1 156 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 184))))))))))))))))))))))))))))) (allB_succ' 30 155 184
  (Eq.refl Bool.true) (allA_of_3_1 30 155 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 154 184 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 154 184 2 15 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 154 184 (accept_3_3 29 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 184 2 14 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 184 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 154 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 184 2 13 77 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 184
  (Polychromatic418967fa.accept_9_7_1_4_1_217 25 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 184 2 12 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 184 (accept_3_3 23 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 184 2 11 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 184 (Polychromatic418967fa.accept_9_3_1_4_1_216 21 154 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 184 2 10 77 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 184
  (Polychromatic418967fa.accept_12_7_10_4_1_382 19 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 184 2 9 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 154 184 (accept_3_3 17 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  154 184 2 8 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 154 184 (Polychromatic418967fa.accept_9_6_1_4_1_474 15 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 184 2 7 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 184 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 154 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 184 2 6 77 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 184 (accept_3_3 11 154 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 184 2 5 77 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 184
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 154 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 184 2 4 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 154 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 184 2 3 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 184 (accept_3_3 5 154 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 184 2 2 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 184 (Polychromatic418967fa.accept_9_3_1_4_1_216 3 154 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 184 2 1 77 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 184 (Polychromatic418967fa.accept_12_1_10_4_1_380 1
  154 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 184)))))))))))))))))))))))))))))))
  (allB_succ' 32 153 184 (Eq.refl Bool.true) (allA_succ_of_accept 31 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1
  31 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 184
  (Polychromatic418967fa.accept_12_6_9_4_1_96 30 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 184 (accept_3_3 29 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 184 (Polychromatic418967fa.accept_16_12_9_8_1_2508 28 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 184 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 184 (accept_3_3 26 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 184
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 184 (accept_3_3 23 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 184 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 184 (accept_3_3 20 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 153 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 184
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 184 (accept_3_3 17 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 184 (Polychromatic418967fa.accept_13_3_10_2_1_381 16 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 184 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 153 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 184 (accept_3_3 14 153 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 184
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 184 (accept_3_3 11 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 184 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 184 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 153 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 184 (accept_3_3 8 153 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7
  153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 184
  (Polychromatic418967fa.accept_12_6_9_4_1_96 6 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 184 (accept_3_3 5 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 184 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 184 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 184 (accept_3_3 2 153 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 184)))))))))))))))))))))))))))))))) (allB_succ' 33
  152 184 (Eq.refl Bool.true) (allA_of_3_1 33 152 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 151 184
  (Eq.refl Bool.true) (allA_succ_of_accept 33 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 184 (accept_3_3 32 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 184 (Polychromatic418967fa.accept_16_15_7_8_1_8189 31 151
  184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 184
  (Polychromatic418967fa.accept_9_3_7_4_1_53 30 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 151 184 (accept_3_3 29 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 151 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 28 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 184 (accept_3_3 26 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 184 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 184
  (Polychromatic418967fa.accept_9_6_7_4_1_212 24 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 184 (accept_3_3 23 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 184 (Polychromatic418967fa.accept_12_10_7_4_1_820 22 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 184 (accept_3_3 20 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 184 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 184
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 184 (accept_3_3 17 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 184 (Polychromatic418967fa.accept_17_16_15_14_1_6747 16 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 184 (accept_3_3 14 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 184 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 151 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 184
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 184 (accept_3_3 11 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 10 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 184 (accept_3_3 8 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 184 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 184
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 184 (accept_3_3 5 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 184 (Polychromatic418967fa.accept_16_4_7_8_1_5753 4 151 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 184 (accept_3_3 2 151 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 1 151 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 184)))))))))))))))))))))))))))))))))) (allB_succ' 35
  150 184 (Eq.refl Bool.true) (allA_succ_of_gcd 34 150 184 2 17 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 184 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 184 2 16 75 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 184
  (Polychromatic418967fa.accept_13_5_7_2_1_852 31 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 184 2 15 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 184 (accept_3_3 29 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 184 2 14 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 184 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 150 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 184 2 13 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 184
  (Polychromatic418967fa.accept_9_7_6_4_1_483 25 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 184 2 12 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 184 (accept_3_3 23 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 184 2 11 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 184 (Polychromatic418967fa.accept_9_3_6_4_1_210 21 150 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 184 2 10 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 184
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 184 2 9 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 184 (accept_3_3 17 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  150 184 2 8 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 150 184 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 150 184 2 7 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 150 184 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 150 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 184 2 6 75 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 184 (accept_3_3 11 150 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 184 2 5 75 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 184
  (Polychromatic418967fa.accept_12_9_6_4_1_402 9 150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 184 2 4 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 184 (Polychromatic418967fa.accept_9_7_6_4_1_483 7 150 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 184 2 3 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 184 (accept_3_3 5 150 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 184 2 2 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 150 184 (Polychromatic418967fa.accept_9_3_6_4_1_210 3 150 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 184 2 1 75 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 184 (Polychromatic418967fa.accept_7_1_3_2_1_13 1
  150 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  184))))))))))))))))))))))))))))))))))) (allB_succ' 36 149 184 (Eq.refl Bool.true) (allA_of_3_1 36 149 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 148 184 (Eq.refl Bool.true) (allA_succ_of_gcd 36 148 184 4 9 37 46
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 148 184
  (accept_3_3 35 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 148 184 2 17 74 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 148 184
  (Polychromatic418967fa.accept_13_7_5_2_1_401 33 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 148 184 4 8 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 148 184 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 148 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 184 2 15 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 184 (accept_3_3 29 148 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 184 4 7 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 184 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 184 2 13 74 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 184
  (Polychromatic418967fa.accept_11_3_5_8_1_458 25 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 184 4 6 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 148 184 (accept_3_3 23 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  148 184 2 11 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 148 184 (Polychromatic418967fa.accept_15_6_13_4_1_2040 21 148 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 184 4 5 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 184 (Polychromatic418967fa.accept_10_9_8_4_1_970
  19 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 184 2 9 74 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 184
  (accept_3_3 17 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 184 4 4 37 46 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 184
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 15 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 148 184 2 7 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 148 184 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 184 4 3 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 184 (accept_3_3 11 148 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 184 2 5 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 184 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 148 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 184 4 2 37 46 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 184
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 184 2 3 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 184 (accept_3_3 5 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  184 4 1 37 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 184 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 184 2 1 74 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 148 184 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 148 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 184))))))))))))))))))))))))))))))))))))) (allB_succ' 38 147 184
  (Eq.refl Bool.true) (allA_succ_of_accept 37 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 184
  (Polychromatic418967fa.accept_16_4_3_8_1_2486 36 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 147 184 (accept_3_3 35 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 147 184 (Polychromatic418967fa.accept_9_7_3_4_1_218 34 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 147 184 (Polychromatic418967fa.accept_9_6_3_4_1_477 33 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 184 (accept_3_3 32 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 184
  (Polychromatic418967fa.accept_12_6_3_4_1_394 30 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 147 184 (accept_3_3 29 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 147 184 (Polychromatic418967fa.accept_9_1_3_4_1_47 28 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 147 184 (Polychromatic418967fa.accept_16_11_3_8_1_4597 27 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 147 184 (accept_3_3 26 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 147 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 184
  (Polychromatic418967fa.accept_9_6_3_4_1_477 24 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 147 184 (accept_3_3 23 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 147 184 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 147 184 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 147 184 (accept_3_3 20 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 184
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 184
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 184 (accept_3_3 17 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 184 (Polychromatic418967fa.accept_9_7_3_4_1_218 16 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 184 (Polychromatic418967fa.accept_9_6_3_4_1_477 15 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 184 (accept_3_3 14 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 184
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 184 (accept_3_3 11 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 147 184 (Polychromatic418967fa.accept_9_1_3_4_1_47 10 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 184 (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 184 (accept_3_3 8 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 184
  (Polychromatic418967fa.accept_9_6_3_4_1_477 6 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 184 (accept_3_3 5 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 184 (Polychromatic418967fa.accept_16_4_3_8_1_2486 4 147 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 184 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 184 (accept_3_3 2 147 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 184 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 147 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 184))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 146 184 (Eq.refl Bool.true) (allA_of_3_1 39 146 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 145 184 (Eq.refl Bool.true) (allA_succ_of_accept 39 145 184 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 184 (accept_3_3 38
  145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 184
  (Polychromatic418967fa.accept_15_7_10_4_1_151 37 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 145 184 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 145 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 184 (accept_3_3 35 145 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 145 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 34 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 184 (Polychromatic418967fa.accept_6_3_1_4_1_25 33
  145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 184 (accept_3_3 32
  145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 184
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 145 184 (Polychromatic418967fa.accept_9_3_1_4_1_216 30 145 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 184 (accept_3_3 29 145 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 145 184 (Polychromatic418967fa.accept_15_13_10_4_1_1232 28 145 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 184 (accept_3_3 26 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 184 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 184 (accept_3_3 23 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 184 (Polychromatic418967fa.accept_12_10_1_4_1_392 22 145 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 184 (accept_3_3 20 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 184 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 184 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 184 (accept_3_3 17 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 16 145 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 184 (accept_3_3 14 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 184 (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 184 (Polychromatic418967fa.accept_9_3_1_4_1_216 12 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 184 (accept_3_3 11 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 184 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 145 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 184 (accept_3_3 8 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 184 (Polychromatic418967fa.accept_9_7_1_4_1_217 7 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 184 (Polychromatic418967fa.accept_9_6_1_4_1_474 6 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 184 (accept_3_3 5 145 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 184 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 184
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 184 (accept_3_3 2 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 184 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 145 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 184)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 144 184 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 144 184 8 5 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 144 184 (Polychromatic418967fa.accept_27_12_9_22_1_10602 39 144 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 184 2 19 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 184
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 184 4 9 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 184 (accept_3_3 35 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  144 184 2 17 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 144 184 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 144 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 184 8 4 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 184
  (Polychromatic418967fa.accept_19_12_11_13_1_4885 31 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 144 184 2 15 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 144 184 (accept_3_3 29 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 184 4 7 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 144 184 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 184 2 13 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 184 (Polychromatic418967fa.accept_13_12_1_2_1_845
  25 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 184 8 3 18 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 184
  (accept_3_3 23 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 184 2 11 72 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 184
  (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 184 4 5 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 184 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 184 2 9 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 184 (accept_3_3 17 144 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 184 8 2 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 184 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 144
  184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 184 2 7 72 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 184
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 184 4 3 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 184 (accept_3_3 11 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  144 184 2 5 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 144 184 (Polychromatic418967fa.accept_13_9_1_2_1_2952 9 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 144 184 8 1 18 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 144 184 (Polychromatic418967fa.accept_17_7_8_14_1_6720 7 144 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 184 2 3 72 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 184 (accept_3_3 5 144 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 184 4 1 36 46 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 184 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 144 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 184 2 1 72 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 184
  (Polychromatic418967fa.accept_22_1_12_8_1_10601 1 144 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 184))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 143 184 (Eq.refl Bool.true) (allA_of_3_1 42
  143 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 43 142 184 (Eq.refl Bool.true) (allA_succ_of_gcd 42 142
  184 2 21 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  142 184 (accept_3_3 41 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 142 184 2 20 71 92
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 142 184
  (Polychromatic418967fa.accept_9_3_7_4_1_53 39 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 142 184 2 19 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 142 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 37 142 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 142 184 2 18 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 142 184 (accept_3_3 35 142 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 142 184 2 17 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 142 184 (Polychromatic418967fa.accept_9_6_7_4_1_212 33
  142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 184 2 16 71 92 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 184
  (Polychromatic418967fa.accept_11_9_10_8_1_444 31 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 184 2 15 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 184 (accept_3_3 29 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 184 2 14 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 184 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 142 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 184 2 13 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 184
  (Polychromatic418967fa.accept_12_1_10_4_1_380 25 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 184 2 12 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 184 (accept_3_3 23 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 184 2 11 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 184 (Polychromatic418967fa.accept_9_3_7_4_1_53 21 142 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 184 2 10 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 184
  (Polychromatic418967fa.accept_9_1_7_4_1_52 19 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 184 2 9 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 184 (accept_3_3 17 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 184 2 8 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 184 (Polychromatic418967fa.accept_9_6_7_4_1_212 15 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 184 2 7 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 184 (Polychromatic418967fa.accept_12_1_10_4_1_380 13 142 184 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 184 2 6 71 92 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 184 (accept_3_3 11 142 184
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 184 2 5 71 92 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 184
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 184 2 4 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 184 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 142 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 184 2 3 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 184 (accept_3_3 5 142 184 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 184 2 2 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 184 (Polychromatic418967fa.accept_9_3_7_4_1_53 3 142 184 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 184 2 1 71 92 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 184 (Polychromatic418967fa.accept_9_1_7_4_1_52 1
  142 184 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  184)))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_184_segment_000))))))))))))))))))))))))))))))))))))))))))


