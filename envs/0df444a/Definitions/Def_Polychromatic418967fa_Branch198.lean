-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch198
-- name    : Polychromatic418967fa_Branch198
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:07.900828+00:00
-- url     : https://prove2.me/theorems/881b71f5-2179-45c1-a18a-fe2b87e71719
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch198_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_198 : allB 198 198 :=
  allB_succ' 2 197 198 (Eq.refl Bool.true) (allA_succ_of_accept 1 197 198 (accept_3_4 1 197 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 198)) (allB_succ' 3 196 198 (Eq.refl Bool.true) (allA_succ_of_gcd 2 196 198 2 1 98
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 196 198
  (Polychromatic418967fa.accept_20_1_16_18_1_1677 1 196 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 196 198))) (allB_succ' 4 195 198 (Eq.refl Bool.true) (allA_succ_of_gcd 3 195 198 3 1 65 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 195 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195 198)))) (allB_succ' 5 194 198 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  194 198 2 2 97 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 194 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 194 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 194 198 2 1 97 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 194 198 (accept_3_4 1 194 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  198))))) (allB_succ' 6 193 198 (Eq.refl Bool.true) (allA_succ_of_accept 5 193 198 (accept_3_5 5 193 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 198 (Polychromatic418967fa.accept_17_4_6_11_1_1030 4 193
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 198 (accept_3_5 2 193 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 193 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 198)))))) (allB_succ' 7 192 198 (Eq.refl Bool.true) (allA_succ_of_gcd 6 192 198 6 1 32 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 192 198 2 2 96 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 192 198 3 1 64 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 192 198 2 1 96 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 192 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 198))))))) (allB_succ' 8 191 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 191 198 (accept_3_4 7 191 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 6 191 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 198 (accept_3_4 4 191 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 191 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 191 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 198 (accept_3_4 1 191 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  198)))))))) (allB_succ' 9 190 198 (Eq.refl Bool.true) (allA_succ_of_gcd 8 190 198 2 4 95 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 198
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 190 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 198 2 3 95 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 198 (accept_3_5 5 190 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  198 2 2 95 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 190 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 198 2 1 95 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 190 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 190 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 198))))))))) (allB_succ' 10 189 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 189 198 9 1 21 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 189 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 189 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 198 3 2 63 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 198
  (Polychromatic418967fa.accept_14_5_7_2_1_468 5 189 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 189 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 198 3 1 63 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 189 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 189 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 189 198)))))))))) (allB_succ' 11 188 198 (Eq.refl Bool.true) (allA_succ_of_gcd 10 188 198 2 5 94 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 188 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 198 2 4 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 198 (accept_3_4 7 188 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  198 2 3 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 188 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 198 2 2 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 188 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 198 2 1 94 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 198 (accept_3_4 1 188 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 198))))))))))) (allB_succ' 12 187 198 (Eq.refl Bool.true) (allA_succ_of_gcd 11 187
  198 11 1 17 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10
  187 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 187 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 198 (accept_3_5 8 187 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 198 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 187 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 6 187 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 198 (accept_3_5 5 187 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 187 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 187 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 198 (accept_3_5 2 187 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 198)))))))))))) (allB_succ' 13 186 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 186 198 6 2 31 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 198 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 186 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 198 2 5 93 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 198 3 3 62 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 198 2 4 93 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 198
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 186 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 198 6 1 31 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 186 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 198 2 2 93 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 198 3 1 62 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 198 2 1 93 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 186 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 198))))))))))))) (allB_succ' 14 185 198
  (Eq.refl Bool.true) (allA_succ_of_accept 13 185 198 (accept_3_4 13 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 185 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 198 (accept_3_4 10 185 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 9
  185 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 198 (accept_3_4 7 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 185 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 198 (accept_3_4 4 185 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 198 (accept_3_4 1 185 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  198)))))))))))))) (allB_succ' 15 184 198 (Eq.refl Bool.true) (allA_succ_of_gcd 14 184 198 2 7 92 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 198
  (Polychromatic418967fa.accept_21_13_16_9_1_2541 13 184 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 184 198 2 6 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 184 198 (accept_3_5 11 184 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 198 2 5 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 184 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 184 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 198 2 4 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 184 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 198 2 3 92 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 198 (accept_3_5 5 184 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 198 2 2 92 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 184 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3
  184 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 198 2 1 92 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 198
  (Polychromatic418967fa.accept_13_1_2_3_1_911 1 184 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 198))))))))))))))) (allB_succ' 16 183 198 (Eq.refl Bool.true) (allA_succ_of_gcd 15 183 198 3 5 61 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 183 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 198 3 4 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 198 (Polychromatic418967fa.accept_10_1_3_8_1_136
  11 183 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 10 183 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 183 198 3 3 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 183 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 183 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 198 3 2 61 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 183 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 198 3 1 61 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 183 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 198)))))))))))))))) (allB_succ' 17 182 198 (Eq.refl Bool.true) (allA_succ_of_gcd 16 182 198 2 8 91 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 182 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 198 2 7 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 182 198 (accept_3_4 13 182 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  182 198 2 6 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 182 198 (Polychromatic418967fa.accept_27_11_20_9_1_11601 11 182 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 198 2 5 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 182 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 182 198 2 4 91 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 182 198 (accept_3_4 7 182 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182 198 2 3 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 182 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5
  182 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 198 2 2 91 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 182 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 182 198 2 1 91 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 182 198 (accept_3_4 1 182 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  198))))))))))))))))) (allB_succ' 18 181 198 (Eq.refl Bool.true) (allA_succ_of_accept 17 181 198 (accept_3_5 17 181 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 198
  (Polychromatic418967fa.accept_19_16_10_8_1_10067 16 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 198 (accept_3_5 14 181 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 181 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 198
  (Polychromatic418967fa.accept_19_12_10_8_1_3270 12 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 181 198 (accept_3_5 11 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 181 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 181 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 181 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 198 (accept_3_5 8 181 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7
  181 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 198
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 198 (accept_3_5 5 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 181 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 198 (accept_3_5 2 181 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 181 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 198)))))))))))))))))) (allB_succ' 19 180 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 180 198 18 1 10 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 198 2 8 90 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 198 3 5 60 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 198 2 7 90 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 198
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 13 180 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 198 6 2 30 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 180 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 198 2 5 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 198 9 1 20 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 198 2 4 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540
  7 180 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 198 6 1 30 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 198
  (Polychromatic418967fa.accept_13_5_11_3_1_902 5 180 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 180 198 2 2 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 180 198 3 1 60 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 180 198 2 1 90 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 180 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 198))))))))))))))))))) (allB_succ' 20 179 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 179 198 (accept_3_4 19 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 198 (Polychromatic418967fa.accept_16_2_3_6_1_3372 18 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 198 (accept_3_4 16 179 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 179 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 198 (accept_3_4 13 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 179 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 198 (accept_3_4 10 179 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 198
  (Polychromatic418967fa.accept_17_8_9_11_1_3976 8 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 198 (accept_3_4 7 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 198 (accept_3_4 4 179 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 198 (Polychromatic418967fa.accept_17_3_9_11_1_11600 3 179 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 198 (accept_3_4 1 179 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  198)))))))))))))))))))) (allB_succ' 21 178 198 (Eq.refl Bool.true) (allA_succ_of_gcd 20 178 198 2 10 89 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 178 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 198 2 9 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 178 198 (accept_3_5 17 178 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  178 198 2 8 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 178 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 178 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 178 198 2 7 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 178 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 178 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 178 198 2 6 89 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 178 198 (accept_3_5 11 178 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 178 198 2 5 89 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 178 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 178 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 178 198 2 4 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 178 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7 178 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 178 198 2 3 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 178 198 (accept_3_5 5 178 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 178 198 2 2 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 178 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 178 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 178 198 2 1 89 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 178 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1
  178 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 198)))))))))))))))))))))
  (allB_succ' 22 177 198 (Eq.refl Bool.true) (allA_succ_of_gcd 21 177 198 3 7 59 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 198 3 6 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 198 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  17 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 177 198 3 5 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 177 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 177 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 198 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 177
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 198 3 4 59 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 177 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 198 3 3 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 177 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 177 198 3 2 59 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 177 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 177 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 198 3 1 59 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 177 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 198 (Polychromatic418967fa.accept_17_1_7_11_1_2892 1 177 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 198)))))))))))))))))))))) (allB_succ' 23 176 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 176 198 22 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 176 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 176 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 198 2 10 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 198 (accept_3_4 19 176 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 198 2 9 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 198 2 8 88 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 15 176 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 198 2 7 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 176 198 (accept_3_4 13 176 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  176 198 2 6 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11
  176 198 11 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd
  10 176 198 2 5 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 176 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 176 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 198 2 4 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 198 (accept_3_4 7 176 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 176 198 2 3 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 176 198 (Polychromatic418967fa.accept_17_5_6_11_1_3974 5 176 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 198 2 2 88 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3
  176 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 198 2 1 88 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 198 (accept_3_4 1
  176 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 198))))))))))))))))))))))) (allB_succ' 24 175 198
  (Eq.refl Bool.true) (allA_succ_of_accept 23 175 198 (accept_3_5 23 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 175 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 175 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 198 (accept_3_5 20 175 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 198 (Polychromatic418967fa.accept_14_5_7_2_1_468
  19 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 18 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 198 (accept_3_5 17 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 198 (Polychromatic418967fa.accept_17_16_5_11_1_7830 16 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 198 (Polychromatic418967fa.accept_17_15_5_11_1_6468 15 175 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 198 (accept_3_5 14 175 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 198 (accept_3_5 11 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 10 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 198 (accept_3_5 8 175 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 175 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 198
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 198 (accept_3_5 5 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 198 (Polychromatic418967fa.accept_27_4_13_9_1_11599 4 175 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 175 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 198 (accept_3_5 2 175 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 198)))))))))))))))))))))))) (allB_succ' 25 174 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 174 198 6 4 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 174 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 174 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 198 2 11 87 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 198 3 7 58 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 198 2 10 87 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 174 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 198 6 3 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 198 2 8 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 198 3 5 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 198 2 7 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949
  13 174 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 198 6 2 29 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 198 2 5 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 174 198 3 3 58 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 174 198 2 4 87 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 198 (Polychromatic418967fa.accept_21_7_6_9_1_8463 7 174 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 198 6 1 29 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 5 174 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 198 2 2 87 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 198 3 1 58 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 198 2 1 87 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 174 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 198))))))))))))))))))))))))) (allB_succ' 26 173 198 (Eq.refl Bool.true) (allA_succ_of_accept 25 173 198
  (accept_3_4 25 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 173 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 198 (accept_3_4 22 173 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 173 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 173 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 198
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 198 (accept_3_4 19 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 198 (accept_3_4 16 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 198
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 14 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 198 (accept_3_4 13 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 198 (accept_3_4 10 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 198 (Polychromatic418967fa.accept_15_9_8_3_1_557 9 173 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 198
  (Polychromatic418967fa.accept_20_8_13_18_1_7110 8 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 198 (accept_3_4 7 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 198 (accept_3_4 4 173 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 198
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 2 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 198 (accept_3_4 1 173 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  198)))))))))))))))))))))))))) (allB_succ' 27 172 198 (Eq.refl Bool.true) (allA_succ_of_gcd 26 172 198 2 13 86 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 198 2 12 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 198 (accept_3_5 23 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 198 2 11 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 172 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 198 2 10 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 198 2 9 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 172 198 (accept_3_5 17 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  172 198 2 8 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 172 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 172 198 2 7 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 172 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 172 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 198 2 6 86 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 198 (accept_3_5 11 172 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 198 2 5 86 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 172 198 2 4 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 172 198 (Polychromatic418967fa.accept_19_7_1_8_1_7300 7 172 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 198 2 3 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 198 (accept_3_5 5 172 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 172 198 2 2 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 172 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 172 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 198 2 1 86 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 198
  (Polychromatic418967fa.accept_23_1_11_14_1_11598 1 172 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 198))))))))))))))))))))))))))) (allB_succ' 28 171 198 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 171 198 9 3 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 171 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 198 3 8 57 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 198 3 7 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 171 198 9 2 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 171
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 198 3 5 57 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 198 3 4 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 198 (Polychromatic418967fa.accept_13_11_2_3_1_883
  11 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 171 198 9 1 19 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 171 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 198 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 171
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 198 3 2 57 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 171 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 198 3 1 57 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 171 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 171 198)))))))))))))))))))))))))))) (allB_succ' 29 170 198 (Eq.refl Bool.true) (allA_succ_of_gcd 28 170 198
  2 14 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170
  198 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 170 198 2 13 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 170 198 (accept_3_4 25 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 198 2 12 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 170 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 198 2 11 85 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 198 2 10 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 198 (accept_3_4 19 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 198 2 9 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 170 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 170 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 198 2 8 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 198 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 170 198 2 7 85 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 198
  (accept_3_4 13 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 198 2 6 85 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 170 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 198 2 5 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 170 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 170 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 198 2 4 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 198 (accept_3_4 7 170 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 170 198 2 3 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 170 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 170 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 170 198 2 2 85 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  170 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 198 2 1 85 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 198 (accept_3_4 1
  170 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 198))))))))))))))))))))))))))))) (allB_succ' 30 169 198
  (Eq.refl Bool.true) (allA_succ_of_accept 29 169 198 (accept_3_5 29 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 169 198 (Polychromatic418967fa.accept_19_9_17_8_1_2075 28 169 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 198 (accept_3_5 26 169 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 198
  (Polychromatic418967fa.accept_19_6_17_8_1_8746 25 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 169 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 169 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 198 (accept_3_5 23 169 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 169 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 198 (accept_3_5 20 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 198 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 198 (accept_3_5 17 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 169
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 198 (accept_3_5 14 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 198 (Polychromatic418967fa.accept_17_12_16_11_1_7885 12 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 198 (accept_3_5 11 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 169 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 198
  (Polychromatic418967fa.accept_19_9_17_8_1_2075 9 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 198 (accept_3_5 8 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 169 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 198 (accept_3_5 5 169 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 169 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 198 (accept_3_5 2 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 169 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 198)))))))))))))))))))))))))))))) (allB_succ' 31 168 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 168 198 6 5 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 168 198 (Polychromatic418967fa.accept_19_10_16_8_1_3289 29 168 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 198 2 14 84 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 168 198 3 9 56 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 168 198 2 13 84 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 198
  (Polychromatic418967fa.accept_19_6_16_8_1_10116 25 168 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 168 198 6 4 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 168 198 (Polychromatic418967fa.accept_20_3_8_18_1_5603 23 168 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 198 2 11 84 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 198 3 7 56 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 198 2 10 84 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 198
  (Polychromatic418967fa.accept_23_19_7_14_1_11491 19 168 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 168 198 6 3 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 168 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 168 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 198 2 8 84 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 198 3 5 56 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 198 2 7 84 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 198
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 13 168 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 168 198 6 2 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 168 198 (Polychromatic418967fa.accept_19_11_16_8_1_2098 11 168 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 198 2 5 84 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 168 198 3 3 56 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 168 198 2 4 84 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 198
  (Polychromatic418967fa.accept_19_7_16_8_1_8761 7 168 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 198 6 1 28 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 198 (Polychromatic418967fa.accept_17_5_15_11_1_3978 5 168 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 198 2 2 84 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 198 3 1 56 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 198 2 1 84 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 198 (Polychromatic418967fa.accept_19_1_16_8_1_10075 1 168
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 198)))))))))))))))))))))))))))))))
  (allB_succ' 32 167 198 (Eq.refl Bool.true) (allA_succ_of_accept 31 167 198 (accept_3_4 31 167 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 198 (Polychromatic418967fa.accept_20_10_7_18_1_11564 30 167 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 198 (accept_3_4 28 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 198 (Polychromatic418967fa.accept_19_7_15_8_1_1089 26 167 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 198 (accept_3_4 25 167 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 198
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 167 198 (accept_3_4 22 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 167 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 167
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 198 (accept_3_4 19 167
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 167 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 198 (accept_3_4 16 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 167 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 167 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 198 (Polychromatic418967fa.accept_13_1_11_3_1_901
  14 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 198 (accept_3_4 13
  167 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 198
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 167 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 198 (accept_3_4 10 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 167 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8
  167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 198 (accept_3_4 7 167
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 198
  (Polychromatic418967fa.accept_21_6_20_9_1_6943 6 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 167 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 198 (accept_3_4 4 167 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 167 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 167 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 198 (Polychromatic418967fa.accept_13_2_11_3_1_873
  2 167 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 198 (accept_3_4 1
  167 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167 198)))))))))))))))))))))))))))))))) (allB_succ' 33 166
  198 (Eq.refl Bool.true) (allA_succ_of_gcd 32 166 198 2 16 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 166 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 166 198 2 15 83 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 166 198 (accept_3_5 29
  166 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 166 198 2 14 83 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 166 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 166 198 2 13 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 166 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 25 166 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 166 198 2 12 83 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 166 198 (accept_3_5 23 166 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 166 198 2 11 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 166 198 (Polychromatic418967fa.accept_12_9_10_6_1_872
  21 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 198 2 10 83 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 198
  (Polychromatic418967fa.accept_13_6_10_3_1_897 19 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 198 2 9 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 166 198 (accept_3_5 17 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  166 198 2 8 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 166 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 166 198 2 7 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 166 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 166 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 198 2 6 83 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 198 (accept_3_5 11 166 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 198 2 5 83 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 198 2 4 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 166 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 198 2 3 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 198 (accept_3_5 5 166 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 198 2 2 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 166 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 198 2 1 83 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 198 (Polychromatic418967fa.accept_24_1_22_6_1_11505
  1 166 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  198))))))))))))))))))))))))))))))))) (allB_succ' 34 165 198 (Eq.refl Bool.true) (allA_succ_of_gcd 33 165 198 33 1 5 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 165 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 198 3 10 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 198 (Polychromatic418967fa.accept_21_8_18_9_1_5329
  29 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 198 3 9 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 165 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 198 (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 165
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 198 3 8 55 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 165 198 11 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 165 198 3 7 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 165 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 165 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 198 3 6 55 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 165 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 198 3 5 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 13 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 198 3 4 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 11 165 198 11 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 165 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 165 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 198 3 3 55 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 198 3 2 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 165 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 165 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 198 3 1 55 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 165 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 1 165 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 198))))))))))))))))))))))))))))))))))
  (allB_succ' 35 164 198 (Eq.refl Bool.true) (allA_succ_of_gcd 34 164 198 2 17 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 198 2 16 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 198 (accept_3_4 31 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 198 2 15 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 198 2 14 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 198 2 13 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 198 (accept_3_4 25 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 198 2 12 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 198 (Polychromatic418967fa.accept_19_4_12_8_1_10123 23 164 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 198 2 11 82 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 198 2 10 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 198 (accept_3_4 19 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 198 2 9 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 164 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 17 164 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 198 2 8 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15
  164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 198 2 7 82 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 198 (accept_3_4 13
  164 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 198 2 6 82 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 198
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 198 2 5 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 164 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 164 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 198 2 4 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 198 (accept_3_4 7 164 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 164 198 2 3 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 164 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 198 2 2 82 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 3
  164 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 198 2 1 82 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 198 (accept_3_4 1
  164 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 198))))))))))))))))))))))))))))))))))) (allB_succ' 36
  163 198 (Eq.refl Bool.true) (allA_succ_of_accept 35 163 198 (accept_3_5 35 163 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 163 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 34 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 198 (accept_3_5 32 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 163 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 198 (accept_3_5 29 163 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 198 (Polychromatic418967fa.accept_19_9_11_8_1_10050 28 163 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 198
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 198 (accept_3_5 26 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 198 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 198 (accept_3_5 23 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 198 (Polychromatic418967fa.accept_13_9_7_3_1_1531 22 163
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 198 (accept_3_5 20 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 198 (Polychromatic418967fa.accept_25_19_13_23_1_11597 19 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 198 (accept_3_5 17 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 163
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 198 (accept_3_5 14 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 198 (accept_3_5 11 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 10 163
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 198 (accept_3_5 8 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 198 (Polychromatic418967fa.accept_14_7_9_2_1_2489 7 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 163 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 198 (accept_3_5 5 163 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 4 163 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 198
  (Polychromatic418967fa.accept_17_3_10_11_1_7848 3 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 198 (accept_3_5 2 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 198)))))))))))))))))))))))))))))))))))) (allB_succ' 37 162 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 162 198 18 2 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 162 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 162 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 198 2 17 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 162 198 3 11 54 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 162 198 2 16 81 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 198 6 5 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 162 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 162 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 198 2 14 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 198 9 3 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 198 2 13 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 198 6 4 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 162 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 198 2 11 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 198 3 7 54 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 198 2 10 81 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 198
  (Polychromatic418967fa.accept_16_3_2_6_1_4461 19 162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 198 18 1 9 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 198 2 8 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 198 3 5 54 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 198 2 7 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13
  162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 198 6 2 27 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 198
  (Polychromatic418967fa.accept_16_11_2_6_1_1435 11 162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 198 2 5 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 162 198 9 1 18 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 162 198 2 4 81 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 198 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 162 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 198 6 1 27 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 162 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 198 2 2 81 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 198 3 1 54 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 198 2 1 81 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 198
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 1 162 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 198))))))))))))))))))))))))))))))))))))) (allB_succ' 38 161 198 (Eq.refl Bool.true) (allA_succ_of_accept
  37 161 198 (accept_3_4 37 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 198
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 198 (accept_3_4 34 161 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 161 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 33 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 32 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 198 (accept_3_4 31 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 198 (Polychromatic418967fa.accept_19_11_9_8_1_11507 30 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 198 (accept_3_4 28 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 198
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 198 (accept_3_4 25 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 198 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 198 (accept_3_4 22 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 198 (Polychromatic418967fa.accept_13_8_5_3_1_427 21 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 198
  (Polychromatic418967fa.accept_19_1_9_8_1_4474 20 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 198 (accept_3_4 19 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 198 (Polychromatic418967fa.accept_19_17_9_8_1_3269 17 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 198 (accept_3_4 16 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 198
  (Polychromatic418967fa.accept_13_1_5_3_1_888 14 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 198 (accept_3_4 13 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 198 (accept_3_4 10 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 198
  (Polychromatic418967fa.accept_13_8_5_3_1_427 8 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 198 (accept_3_4 7 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 198 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 198 (Polychromatic418967fa.accept_14_5_7_2_1_468 5 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 198 (accept_3_4 4 161 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 198
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 198 (accept_3_4 1 161 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  198)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 160 198 (Eq.refl Bool.true) (allA_succ_of_gcd 38 160 198 2 19
  80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 160 198
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 37 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 160 198 2 18 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 160 198 (accept_3_5 35 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 160 198 2 17 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 160 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 160 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 198 2 16 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 198 2 15 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 198 (accept_3_5 29 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 198 2 14 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 160 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 198 2 13 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 198 2 12 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 160 198 (accept_3_5 23 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 198 2 11 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 160 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 198 2 10 80 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 198
  (Polychromatic418967fa.accept_25_19_10_23_1_11596 19 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 160 198 2 9 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 160 198 (accept_3_5 17 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 198 2 8 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 160 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 160 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 198 2 7 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 198
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 13 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 160 198 2 6 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 160 198 (accept_3_5 11 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 198 2 5 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 160 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 160 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 198 2 4 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 160 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 198 2 3 80 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 198 (accept_3_5 5 160 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 198 2 2 80 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 160 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 198 2 1 80 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 1 160 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 198))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 159 198 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 159 198 3 13 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 159 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 159 198 3 12 53 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 159 198
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 198 3 11 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 32
  159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 159 198 3 10 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 159 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 198 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 198 3 9 53 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 198 3 8 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194
  23 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 22 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 159 198 3 7 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 159 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 198 (Polychromatic418967fa.accept_21_19_12_9_1_9957 19 159
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 198 3 6 53 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 159 198 3 5 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 198 (Polychromatic418967fa.accept_10_4_9_8_1_125
  14 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 159 198 3 4 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 159 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 198 3 3 53 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 198 3 2 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 4 159 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 198 3 1 53 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 159 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 198))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 158 198 (Eq.refl Bool.true) (allA_succ_of_gcd 40 158 198 2 20 79 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 198 2 19 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 198 (accept_3_4 37 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 198 2 18 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 198 (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 158 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 198 2 17 79 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 198 2 16 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 198 (accept_3_4 31 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 198 2 15 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 198 (Polychromatic418967fa.accept_23_6_20_14_1_8199 29 158 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 198 2 14 79 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 198 2 13 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 198 (accept_3_4 25 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 198 2 12 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 158 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 198 2 11 79 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 198 2 10 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 198 (accept_3_4 19 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 198 2 9 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 198 (Polychromatic418967fa.accept_19_17_6_8_1_5928 17 158 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 198 2 8 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 198 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 198 2 7 79 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 198
  (accept_3_4 13 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 198 2 6 79 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 198
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 198 2 5 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 158 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 198 2 4 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 198 (accept_3_4 7 158 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 198 2 3 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 198 2 2 79 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  158 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 198 2 1 79 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 198 (accept_3_4 1
  158 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 198)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 157 198 (Eq.refl Bool.true) (allA_succ_of_accept 41 157 198 (accept_3_5 41 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 198 (accept_3_5 38 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 37 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 198 (accept_3_5 35 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 198 (accept_3_5 32 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 198 (accept_3_5 29 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 198 (Polychromatic418967fa.accept_13_2_1_3_1_419 28 157
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 198 (accept_3_5 26 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 198 (accept_3_5 23 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 157 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 198
  (Polychromatic418967fa.accept_19_2_5_8_1_2081 21 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 198 (accept_3_5 20 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 18 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 198 (accept_3_5 17 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 198 (Polychromatic418967fa.accept_19_16_5_8_1_3253 16 157
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 198 (accept_3_5 14 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 198 (accept_3_5 11 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 198 (Polychromatic418967fa.accept_15_10_7_3_1_1939 10 157 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 198 (accept_3_5 8 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 198 (accept_3_5 5 157 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 4 157 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 198 (accept_3_5 2 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 157 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 198)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 156 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 156 198 6 7 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 156 198 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 156 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 198 2 20 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 198 3 13 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 156 198 2 19 78 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 198
  (Polychromatic418967fa.accept_19_18_4_8_1_3282 37 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 198 6 6 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 156 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 198 2 17 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 198 3 11 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 198 2 16 78 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 198
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 31 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 198 6 5 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 198 (Polychromatic418967fa.accept_19_10_4_8_1_11500 29 156 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 198 2 14 78 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 198 3 9 52 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 198 2 13 78 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 198
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 198 6 4 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 156 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 198 2 11 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 198 3 7 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 198 2 10 78 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 198
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 19 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 198 6 3 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 198 (Polychromatic418967fa.accept_19_17_4_8_1_4500 17 156 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 198 2 8 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 198 3 5 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 198 2 7 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169
  13 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 198 6 2 26 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 198
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 198 2 5 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 156 198 3 3 52 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 156 198 2 4 78 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 198 (Polychromatic418967fa.accept_23_7_18_14_1_11585 7 156 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 198 6 1 26 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 156 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 198 2 2 78 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 198 3 1 52 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 198 2 1 78 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 198
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 156 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 198))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 155 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 155 198 (accept_3_4 43 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 198 (accept_3_4 40 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 198 (accept_3_4 37 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 36 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 198 (accept_3_4 34 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 198 (accept_3_4 31 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 198 (accept_3_4 28 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 198
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 26 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 198 (accept_3_4 25 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 198 (accept_3_4 22 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 198 (accept_3_4 19 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 198 (Polychromatic418967fa.accept_16_2_11_6_1_737 18 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 198 (accept_3_4 16 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 198 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 198
  (Polychromatic418967fa.accept_19_14_3_8_1_5920 14 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 198 (accept_3_4 13 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 198 (Polychromatic418967fa.accept_19_11_3_8_1_11517 11 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 198 (accept_3_4 10 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 198
  (Polychromatic418967fa.accept_14_8_1_2_1_965 8 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 198 (accept_3_4 7 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 198 (accept_3_4 4 155 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 155 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 198 (accept_3_4 1 155 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  198)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 154 198 (Eq.refl Bool.true) (allA_succ_of_gcd 44 154
  198 22 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  154 198 (Polychromatic418967fa.accept_19_5_2_8_1_8803 43 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 154 198 2 21 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 154 198 (accept_3_5 41 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 154 198 2 20 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 154 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 39 154 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 154 198 2 19 77 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 198
  (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 198 2 18 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 198 (accept_3_5 35 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 198 2 17 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 154 198 11 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 154 198 2 16 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 154
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 198 2 15 77 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 198 (accept_3_5 29
  154 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 198 2 14 77 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 27 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 154 198 2 13 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 154 198 (Polychromatic418967fa.accept_17_8_1_11_1_4004 25 154 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 154 198 2 12 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 154 198 (accept_3_5 23 154 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 154 198 22 1 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 154 198 (Polychromatic418967fa.accept_12_9_10_6_1_872
  21 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 198 2 10 77 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 198 2 9 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 154 198 (accept_3_5 17 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  154 198 2 8 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 154 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 154 198 2 7 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 154 198 (Polychromatic418967fa.accept_19_13_2_8_1_4484 13 154 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 198 2 6 77 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 154 198 11 1 14 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 154 198 2 5 77 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 198 2 4 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 154 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 198 2 3 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 198 (accept_3_5 5 154 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 198 2 2 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 198 2 1 77 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 1
  154 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  198))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 153 198 (Eq.refl Bool.true) (allA_succ_of_gcd 45 153
  198 9 5 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  153 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 153 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 153 198 3 14 51 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 41 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 153 198 3 13 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 153 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 153 198 9 4 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 153 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 198 3 11 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 153 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 198 3 10 51 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 198 9 3 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660
  26 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 198 3 8 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 153 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 198 3 7 51 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 198 9 2 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17
  153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 198 3 5 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 198 (Polychromatic418967fa.accept_16_13_9_6_1_2306 13 153
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 198 3 4 51 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 198 9 1 17 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 198 3 2 51 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 153 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 198 3 1 51 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 153 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 153 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 198)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 152 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 152 198 2 23 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 152 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 152 198 2 22 76 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 152 198 (accept_3_4 43
  152 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 152 198 2 21 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 152 198 2 20 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 152 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 152 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 152 198 2 19 76 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 152 198 (accept_3_4 37 152 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 152 198 2 18 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 152 198 (Polychromatic418967fa.accept_10_5_2_8_1_135
  35 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 198 2 17 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 198 2 16 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 198 (accept_3_4 31 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 198 2 15 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 198 (Polychromatic418967fa.accept_15_14_2_3_1_1980 29 152 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 198 2 14 76 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 198 2 13 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 198 (accept_3_4 25 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 198 2 12 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 198 (Polychromatic418967fa.accept_27_23_17_9_1_11503 23 152 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 198 2 11 76 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 198 2 10 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 198 (accept_3_4 19 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 198 2 9 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 198 2 8 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 198 (Polychromatic418967fa.accept_10_5_2_8_1_135
  15 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 198 2 7 76 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 198
  (accept_3_4 13 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 198 2 6 76 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 198 2 5 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 152 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 198 2 4 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 198 (accept_3_4 7 152 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 198 2 3 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 152 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 198 2 2 76 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3
  152 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 198 2 1 76 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 198 (accept_3_4 1
  152 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 198)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 151 198 (Eq.refl Bool.true) (allA_succ_of_accept 47 151 198 (accept_3_5 47 151 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 46 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 198 (accept_3_5 44 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 198 (Polychromatic418967fa.accept_19_4_18_8_1_10117 42 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 198 (accept_3_5 41 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 151 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 39 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 198 (accept_3_5 38 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 198 (accept_3_5 35 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 151 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 198 (accept_3_5 32 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 198 (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 198 (accept_3_5 29 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 198 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 151
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 198 (accept_3_5 26 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 198 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 198 (accept_3_5 23 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045 22 151
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 198 (accept_3_5 20 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 18 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 198 (accept_3_5 17 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 198 (Polychromatic418967fa.accept_17_16_15_11_1_10421 16
  151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 198
  (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 198 (accept_3_5 14 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 151 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 198 (accept_3_5 11 151 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 198 (Polychromatic418967fa.accept_19_10_18_8_1_3238 10 151 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 198 (accept_3_5 8 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 151 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 198 (accept_3_5 5 151 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 4 151 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 3 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 198 (accept_3_5 2 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 198)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 150 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 150 198 6 8 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 150 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 198 2 23 75 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 150 198 3 15 50 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 150 198 2 22 75 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 198 6 7 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 150 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 198 2 20 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 198 3 13 50 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 198 2 19 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 198 6 6 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 150 198 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 150 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 198 2 17 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 198 3 11 50 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 198 2 16 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 198
  (Polychromatic418967fa.accept_21_10_3_9_1_11595 31 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 150 198 6 5 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 150 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 198 2 14 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 150 198 3 9 50 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 150 198 2 13 75 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 198
  (Polychromatic418967fa.accept_17_8_14_11_1_9101 25 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 150 198 6 4 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 150 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 198 2 11 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 198 3 7 50 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 198 2 10 75 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 198 6 3 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 150 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 198 2 8 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 198 3 5 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 198 2 7 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13
  150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 198 6 2 25 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 11 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 198 2 5 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 150 198 3 3 50 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 150 198 2 4 75 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 198 (Polychromatic418967fa.accept_20_7_10_18_1_10001 7 150 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 198 6 1 25 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 198 2 2 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 198 3 1 50 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 198 2 1 75 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 150 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 198))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 149 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 149 198 (accept_3_4 49 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 198 (Polychromatic418967fa.accept_13_9_6_3_1_1514 48 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 198 (accept_3_4 46 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 198 (Polychromatic418967fa.accept_19_7_16_8_1_8761 45 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 44 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 198 (accept_3_4 43 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 198 (Polychromatic418967fa.accept_24_18_5_6_1_11559 42 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 41 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 198 (accept_3_4 40 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 198
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 38 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 198 (accept_3_4 37 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 198 (accept_3_4 34 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 33 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 198
  (Polychromatic418967fa.accept_14_4_9_2_1_95 32 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 198 (accept_3_4 31 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 198 (Polychromatic418967fa.accept_19_11_16_8_1_2098 30 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 198 (Polychromatic418967fa.accept_17_12_13_11_1_2910 29 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 198 (accept_3_4 28 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 198
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 149 198 (accept_3_4 25 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 149 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 149 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 198 (accept_3_4 22 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 198 (Polychromatic418967fa.accept_10_1_9_8_1_123
  21 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 198
  (Polychromatic418967fa.accept_16_4_5_6_1_8071 20 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 198 (accept_3_4 19 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 198 (accept_3_4 16 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 198 (accept_3_4 13 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 198 (Polychromatic418967fa.accept_17_12_13_11_1_2910 12 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 198 (accept_3_4 10 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 198 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 149 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 198
  (Polychromatic418967fa.accept_24_8_5_6_1_11594 8 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 198 (accept_3_4 7 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 198 (Polychromatic418967fa.accept_17_6_13_11_1_995 6 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 198 (accept_3_4 4 149 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 198
  (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 198 (accept_3_4 1 149 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  198)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 148 198 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  148 198 2 25 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 148 198 (Polychromatic418967fa.accept_27_22_13_9_1_3653 49 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 148 198 2 24 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 148 198 (accept_3_5 47 148 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 148 198 2 23 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 148 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45
  148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 198 2 22 74 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 43 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 198 2 21 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 198 (accept_3_5 41 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 198 2 20 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 198 2 19 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 198
  (Polychromatic418967fa.accept_13_11_5_3_1_889 37 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 198 2 18 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 198 (accept_3_5 35 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 198 2 17 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 198 2 16 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 198 2 15 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 198 (accept_3_5 29 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 198 2 14 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 198 2 13 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 198
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 148 198 2 12 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 148 198 (accept_3_5 23 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 198 2 11 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 198 2 10 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 19 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 198 2 9 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 198 (accept_3_5 17 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 198 2 8 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 198 2 7 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 148 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 198 2 6 74 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 198 (accept_3_5 11 148 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 198 2 5 74 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 198 2 4 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 198 (Polychromatic418967fa.accept_19_7_15_8_1_1089 7 148 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 198 2 3 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 198 (accept_3_5 5 148 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 198 2 2 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 148 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 198 2 1 74 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 1
  148 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  198))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 147 198 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  147 198 3 17 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 147 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 147 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 147 198 3 16 49 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 147 198
  (Polychromatic418967fa.accept_14_5_7_2_1_468 47 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 46 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 147 198 3 15 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 147 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  44 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 198
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 147 198 3 14 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 40 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 147 198 3 13 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 147 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 38 147 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 147 198 3 12 49 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 198
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 198 3 11 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  32 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 198
  (Polychromatic418967fa.accept_20_11_7_18_1_8632 31 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 147 198 3 10 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 147 198 3 9 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 198 3 8 49 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 198
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 23 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 198 3 7 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 198 3 6 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 147
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 198 3 5 49 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 198 3 4 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 198 (Polychromatic418967fa.accept_16_11_3_6_1_4462
  11 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 198 3 3 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 147 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 198 3 2 49 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 147 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 198 3 1 49 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 147 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 198)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 146 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 52 146 198 2 26 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 146 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 51 146 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 146 198 2 25 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 146 198 (accept_3_4 49 146 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 146 198 2 24 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 146 198
  (Polychromatic418967fa.accept_27_20_11_9_1_11593 47 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 146 198 2 23 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 146 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 146 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 146 198 2 22 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 146 198 (accept_3_4 43 146 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 146 198 2 21 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 146 198
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 41 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 146 198 2 20 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 146 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 146 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 146 198 2 19 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 146 198 (accept_3_4 37 146 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 146 198 2 18 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 146 198 (Polychromatic418967fa.accept_16_3_2_6_1_4461
  35 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 198 2 17 73 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 198 2 16 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 198 (accept_3_4 31 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 198 2 15 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 198 2 14 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 198 2 13 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 198 (accept_3_4 25 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 198 2 12 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 146 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 198 2 11 73 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 198 2 10 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 198 (accept_3_4 19 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 198 2 9 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 198 2 8 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 198 2 7 73 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 198 (accept_3_4 13
  146 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 198 2 6 73 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 198 2 5 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 146 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 198 2 4 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 198 (accept_3_4 7 146 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 198 2 3 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 198 (Polychromatic418967fa.accept_19_5_13_8_1_3229 5 146 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 198 2 2 73 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  146 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 198 2 1 73 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 198 (accept_3_4 1
  146 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  198))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 145 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 145 198 (accept_3_5 53 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 198 (accept_3_5 50 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 145 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 198 (accept_3_5 47 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 198 (accept_3_5 44 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 198 (accept_3_5 41 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 40 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 198 (accept_3_5 38 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 198 (accept_3_5 35 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 198 (Polychromatic418967fa.accept_16_2_1_6_1_2342 34 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 198 (accept_3_5 32 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 198
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 30 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 145 198 (accept_3_5 29 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 145 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 28 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 198 (accept_3_5 26
  145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 145 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 145 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 198 (accept_3_5 23 145 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 145 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 198
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 21 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 198 (accept_3_5 20 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 198 (accept_3_5 17 145 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 198 (Polychromatic418967fa.accept_20_16_5_18_1_2846 16 145 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 198 (accept_3_5 14 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 198 (accept_3_5 11 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 145 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 198 (accept_3_5 8 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 198 (accept_3_5 5 145 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 145 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 198 (accept_3_5 2 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 1 145 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 198)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 144 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 144 198 18 3 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 144 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 198 2 26 72 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 198 3 17 48 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 144 198 2 25 72 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 198 6 8 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 144 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 198 2 23 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 198 9 5 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 198 2 22 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 198
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 43 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 198 6 7 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 198 2 20 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 198 3 13 48 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 198 2 19 72 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 37 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 198 18 2 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 198 2 17 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 198 3 11 48 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 198 2 16 72 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 198
  (Polychromatic418967fa.accept_13_5_1_3_1_878 31 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 198 6 5 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 198 2 14 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 198 9 3 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 198 2 13 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 198
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 198 6 4 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 198 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 198 2 11 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 198 3 7 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 198 2 10 72 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 198 18 1 8 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 17 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 198 2 8 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 198 3 5 48 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 198 2 7 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13
  144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 198 6 2 24 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 198 2 5 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 144 198 9 1 16 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 144 198 2 4 72 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 144 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 198 6 1 24 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 198 2 2 72 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 198 3 1 48 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 198 2 1 72 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 198
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 1 144 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 198))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 143 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 55 143 198 11 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 143 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 143 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 198 (accept_3_4 52
  143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 51 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 143 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 198 (accept_3_4 49 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 143 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 198 (Polychromatic418967fa.accept_7_5_3_2_1_249
  47 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 198 (accept_3_4 46
  143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 143 198 11 4 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 143 198 (accept_3_4 43 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 198 (accept_3_4 40 143 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 198 (Polychromatic418967fa.accept_15_9_8_3_1_557
  39 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 198
  (Polychromatic418967fa.accept_23_15_5_14_1_11592 38 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 143 198 (accept_3_4 37 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 143 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 143
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 198 (accept_3_4 34 143
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 143 198 11 3 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 143 198
  (Polychromatic418967fa.accept_23_9_5_14_1_4710 32 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 198 (accept_3_4 31 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 198 (Polychromatic418967fa.accept_17_13_7_11_1_3985 30 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 198 (accept_3_4 28 143 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 143 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 198 (accept_3_4 25 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 198 (Polychromatic418967fa.accept_15_9_8_3_1_557 24 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 198 (Polychromatic418967fa.accept_16_7_15_6_1_1428 23 143 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 143 198 11 2 13 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 143 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 143 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 198 (accept_3_4 19 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 143 198 (Polychromatic418967fa.accept_17_1_7_11_1_2892 18 143 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 198 (accept_3_4 16 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 198 (Polychromatic418967fa.accept_21_14_17_9_1_5326 14 143 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 198 (accept_3_4 13 143 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 11 143 198 11 1 13 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 10 143 198 (accept_3_4 10
  143 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 143 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 198 (accept_3_4 7 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 143 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5
  143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 198 (accept_3_4 4 143
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 198
  (Polychromatic418967fa.accept_21_3_17_9_1_9958 3 143 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 143 198 (Polychromatic418967fa.accept_19_2_10_8_1_3218 2 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 198 (accept_3_4 1 143 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 143 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 142 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 56 142 198 2 28 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 142 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 55 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 142 198 2 27 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 142 198 (accept_3_5 53 142 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 142 198 2 26 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 142 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 51 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 142 198 2 25 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 142 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 49 142 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 142 198 2 24 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 142 198 (accept_3_5 47 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 142 198 2 23 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 142 198 (Polychromatic418967fa.accept_10_5_2_8_1_135
  45 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 198 2 22 71 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 198
  (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 198 2 21 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 198 (accept_3_5 41 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 198 2 20 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 198 2 19 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 198
  (Polychromatic418967fa.accept_19_18_9_8_1_3267 37 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 198 2 18 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 198 (accept_3_5 35 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 198 2 17 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 198 2 16 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 198
  (Polychromatic418967fa.accept_21_10_16_9_1_5302 31 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 142 198 2 15 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 142 198 (accept_3_5 29 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 198 2 14 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 198 2 13 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 198 2 12 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 198 (accept_3_5 23 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 198 2 11 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 142 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 198 2 10 71 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 198
  (Polychromatic418967fa.accept_15_4_7_3_1_119 19 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 198 2 9 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 198 (accept_3_5 17 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 198 2 8 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 198 2 7 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 198 (Polychromatic418967fa.accept_17_13_6_11_1_4014 13 142 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 198 2 6 71 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 198 (accept_3_5 11
  142 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 198 2 5 71 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 198 2 4 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 198 (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 142 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 198 2 3 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 198 (accept_3_5 5 142 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 198 2 2 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 142 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 198 2 1 71 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 198 (Polychromatic418967fa.accept_19_1_9_8_1_4474 1
  142 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 141 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 141 198 3 19 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 141 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 141 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 141 198 3 18 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 141 198
  (Polychromatic418967fa.accept_10_3_1_8_1_132 53 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 141 198 3 17 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 141 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  50 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 49 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 141 198 3 16 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 141 198 3 15 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 141 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 141 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 141 198 3 14 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 198 3 13 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 38
  141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 198
  (Polychromatic418967fa.accept_20_17_1_18_1_11536 37 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 141 198 3 12 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 34 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 198 3 11 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 32 141 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 198 3 10 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 29 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 198 3 9 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 198
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 198 3 8 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 141
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 198 3 7 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 198 3 6 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17
  141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 198 3 5 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 141 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 198 3 4 47 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 198 3 3 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 141 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 198 3 2 47 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 141 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 198 3 1 47 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 141 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 1 141 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 140 198 (Eq.refl Bool.true) (allA_succ_of_gcd 58 140 198 2 29 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 198 2 28 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 198 (accept_3_4 55 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 198 2 27 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 53 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 198 2 26 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 198 2 25 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 198 (accept_3_4 49 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 198 2 24 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 198 (Polychromatic418967fa.accept_15_2_5_3_1_552 47 140 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 198 2 23 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 198 2 22 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 198 (accept_3_4 43 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 198 2 21 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 198 2 20 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 198 2 19 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 198 (accept_3_4 37 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 198 2 18 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 198 (Polychromatic418967fa.accept_19_16_7_8_1_8820 35 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 198 2 17 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 198 2 16 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 198 (accept_3_4 31 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 198 2 15 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 198 (Polychromatic418967fa.accept_27_2_5_9_1_3548 29 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 198 2 14 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 198 2 13 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 198 (accept_3_4 25 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 198 2 12 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 198 (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 198 2 11 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 198 2 10 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 198 (accept_3_4 19 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 198 2 9 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 198 (Polychromatic418967fa.accept_15_2_5_3_1_552 17 140 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 198 2 8 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 198 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 198 2 7 70 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 198
  (accept_3_4 13 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 198 2 6 70 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 198 2 5 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 198 2 4 70 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 198 (accept_3_4 7 140 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 198 2 3 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 198 (Polychromatic418967fa.accept_21_5_14_9_1_2410 5 140 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 198 2 2 70 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 3 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 198 2 1 70 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 198 (accept_3_4 1 140 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 139 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 139 198 (accept_3_5 59 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 58 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 198 (accept_3_5 56 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 198 (Polychromatic418967fa.accept_19_17_6_8_1_5928 55 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 198 (accept_3_5 53 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 52 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 198 (accept_3_5 50 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 198
  (Polychromatic418967fa.accept_17_14_3_11_1_11591 48 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 139 198 (accept_3_5 47 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 139 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 46 139 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 198 (accept_3_5 44 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 198
  (Polychromatic418967fa.accept_24_18_19_6_1_6101 42 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 139 198 (accept_3_5 41 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 139 198 (Polychromatic418967fa.accept_19_2_6_8_1_3284 40 139 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 198 (accept_3_5 38 139 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37
  139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 36 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 198 (accept_3_5 35 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 198 (accept_3_5 32 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 198
  (Polychromatic418967fa.accept_29_1_23_24_1_11590 30 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 139 198 (accept_3_5 29 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 139 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 28 139 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 139
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 198 (accept_3_5 26 139
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3
  25 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 24 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 198 (accept_3_5 23 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 198 (accept_3_5 20 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 19 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 18 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 198 (accept_3_5 17 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 198 (accept_3_5 14 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 198
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 198 (accept_3_5 11 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 198 (accept_3_5 8 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 6 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 198 (accept_3_5 5 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 139 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 198 (accept_3_5 2 139 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 138 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 138 198 6 10 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 138 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 198 2 29 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 138 198 3 19 46 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 138 198 2 28 69 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 198
  (Polychromatic418967fa.accept_21_13_12_9_1_5323 55 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 138 198 6 9 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 138 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 138 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 198 2 26 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 138 198 3 17 46 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 198 2 25 69 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 198
  (Polychromatic418967fa.accept_14_7_12_2_1_2502 49 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 198 6 8 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 138 198 (Polychromatic418967fa.accept_21_5_12_9_1_11589 47 138 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 198 2 23 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 198 3 15 46 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 198 2 22 69 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 198
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 43 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 198 6 7 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 198 (Polychromatic418967fa.accept_19_3_5_8_1_8790 41 138 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 198 2 20 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 198 3 13 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 198 2 19 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 198
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 198 6 6 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 138 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 198 2 17 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 198 3 11 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 198 2 16 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 198 6 5 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 198 (Polychromatic418967fa.accept_19_10_5_8_1_11588 29 138 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 198 2 14 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 198 3 9 46 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 198 2 13 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 198 6 4 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 198 (Polychromatic418967fa.accept_19_4_5_8_1_11520 23 138 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 198 2 11 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 198 3 7 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 198 2 10 69 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 198
  (Polychromatic418967fa.accept_21_19_12_9_1_9957 19 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 138 198 6 3 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 138 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 198 2 8 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 198 3 5 46 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 198 2 7 69 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 198
  (Polychromatic418967fa.accept_19_13_5_8_1_4487 13 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 198 6 2 23 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 138 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 198 2 5 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 198 3 3 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 198 2 4 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7
  138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 198 6 1 23 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 198
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 138 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 198 2 2 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 138 198 3 1 46 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 138 198 2 1 69 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 198 (Polychromatic418967fa.accept_21_1_12_9_1_8469 1 138 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 137 198 (Eq.refl Bool.true) (allA_succ_of_accept 61 137 198 (accept_3_4 61 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 60 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 198 (accept_3_4 58 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 57 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 56 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 198 (accept_3_4 55 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 198
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 53 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 198 (accept_3_4 52 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 198 (Polychromatic418967fa.accept_13_11_7_3_1_894 50 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 198 (accept_3_4 49 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 137 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 198 (accept_3_4 46 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 45 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 198 (Polychromatic418967fa.accept_15_14_2_3_1_1980 44 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 198 (accept_3_4 43 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 137
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 198 (accept_3_4 40 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 198 (Polychromatic418967fa.accept_23_15_22_14_1_11570 38 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 198 (accept_3_4 37 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 198 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 137
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 198 (accept_3_4 34 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 198 (Polychromatic418967fa.accept_19_13_4_8_1_11571 32 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 198 (accept_3_4 31 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 198 (Polychromatic418967fa.accept_13_4_7_3_1_92 30 137 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 198 (accept_3_4 28 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 198 (accept_3_4 25 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 198 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 198 (accept_3_4 22 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 21 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 198 (accept_3_4 19 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 198 (Polychromatic418967fa.accept_16_2_9_6_1_4441 18 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 198
  (Polychromatic418967fa.accept_13_4_7_3_1_92 17 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 198 (accept_3_4 16 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 198 (accept_3_4 13 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 198 (accept_3_4 10 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 198 (Polychromatic418967fa.accept_13_8_7_3_1_430 8 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 198 (accept_3_4 7 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 198 (accept_3_4 4 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 198 (Polychromatic418967fa.accept_16_2_9_6_1_4441 2 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 198 (accept_3_4 1 137 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  136 198 (Eq.refl Bool.true) (allA_succ_of_gcd 62 136 198 2 31 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 61 136 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 136 198 2 30 68 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 136 198 (accept_3_5 59
  136 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 136 198 2 29 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 136 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 136 198 2 28 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 136 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 136 198 2 27 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 136 198 (accept_3_5 53 136 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 136 198 2 26 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 136 198 (Polychromatic418967fa.accept_12_3_4_6_1_434
  51 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 198 2 25 68 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 198
  (Polychromatic418967fa.accept_13_10_6_3_1_1515 49 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 198 2 24 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 198 (accept_3_5 47 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 198 2 23 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 198 2 22 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 198 2 21 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 198 (accept_3_5 41 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 198 2 20 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 198 2 19 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 198
  (Polychromatic418967fa.accept_21_16_10_9_1_9965 37 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 136 198 2 18 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 136 198 (accept_3_5 35 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 198 2 17 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 198 2 16 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 31 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 198 2 15 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 198 (accept_3_5 29 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 198 2 14 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 198 2 13 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 198
  (Polychromatic418967fa.accept_19_6_3_8_1_7283 25 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 198 2 12 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 198 (accept_3_5 23 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 198 2 11 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 198 2 10 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 198 2 9 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 136 198 (accept_3_5 17 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  136 198 2 8 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 136 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 136 198 2 7 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 136 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 136 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 198 2 6 68 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 198 (accept_3_5 11 136 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 198 2 5 68 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 198 2 4 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 198 (Polychromatic418967fa.accept_21_7_10_9_1_6848 7 136 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 198 2 3 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 198 (accept_3_5 5 136 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 198 2 2 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 136 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 198 2 1 68 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1
  136 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 135 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 135 198 9 7 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 135 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 198 3 20 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 198
  (Polychromatic418967fa.accept_30_29_15_18_1_11587 59 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 135 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 135 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 198 3 19 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 56 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 198 (Polychromatic418967fa.accept_23_9_20_14_1_9875 55 135 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 135 198 9 6 15 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 135 198 3 17 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 135 198 (Polychromatic418967fa.accept_12_2_3_6_1_112
  50 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 135 198 3 16 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 135 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 135 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 135 198 9 5 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 135 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 43 135
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 198 3 14 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 135 198 3 13 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 198 (Polychromatic418967fa.accept_12_2_3_6_1_112
  38 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 198 9 4 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 135 198 (Polychromatic418967fa.accept_13_9_5_3_1_428 35 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 135
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 198 3 11 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 198 (Polychromatic418967fa.accept_16_15_7_6_1_1453 31 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 198 3 10 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 28 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 198 9 3 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 198 3 8 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 198
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 198 3 7 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 19 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 198 9 2 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 135
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 198 3 5 45 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 198 3 4 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 198 (Polychromatic418967fa.accept_13_11_5_3_1_889
  11 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 10 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 198 9 1 15 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 135 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 198 3 2 45 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 135 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 198 3 1 45 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 134 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 134 198 2 32 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 134 198 (Polychromatic418967fa.accept_12_3_2_6_1_138 63 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 134 198 2 31 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 134 198 (accept_3_4 61 134 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 134 198 2 30 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 134 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 134 198 2 29 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 134 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 57 134 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 134 198 2 28 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 134 198 (accept_3_4 55 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 134 198 2 27 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 134 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545
  53 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 198 2 26 67 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 198 2 25 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 198 (accept_3_4 49 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 198 2 24 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 198 2 23 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 198 2 22 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 198 (accept_3_4 43 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 198 2 21 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 134 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 198 2 20 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 198 2 19 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 198 (accept_3_4 37 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 198 2 18 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 198 (Polychromatic418967fa.accept_19_16_1_8_1_3244 35 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 198 2 17 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 33 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 198 2 16 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 198 (accept_3_4 31 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 198 2 15 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 134 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 198 2 14 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 198 2 13 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 198 (accept_3_4 25 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 198 2 12 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 198 (Polychromatic418967fa.accept_29_23_18_24_1_11586 23 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 198 2 11 67 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 198 2 10 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 198 (accept_3_4 19 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 198 2 9 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 198 2 8 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 198 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 198 2 7 67 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 198
  (accept_3_4 13 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 198 2 6 67 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 198
  (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 134 198 2 5 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 134 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 198 2 4 67 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 198 (accept_3_4 7 134 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 198 2 3 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 198 (Polychromatic418967fa.accept_17_5_15_11_1_3978 5 134
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 198 2 2 67 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 198 2 1 67 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 198 (accept_3_4 1 134 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 133 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 133 198 (accept_3_5 65 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 198 (Polychromatic418967fa.accept_24_16_13_6_1_11519 64 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 198 (accept_3_5 62 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 61 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 198
  (Polychromatic418967fa.accept_21_18_7_9_1_2529 60 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 198 (accept_3_5 59 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 198 (Polychromatic418967fa.accept_21_16_7_9_1_6877 58 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 57 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 198 (accept_3_5 56 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 198
  (Polychromatic418967fa.accept_14_12_7_2_1_1663 54 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 198 (accept_3_5 53 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 198 (Polychromatic418967fa.accept_16_4_5_6_1_8071 52 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 198 (accept_3_5 50 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 49 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 198
  (Polychromatic418967fa.accept_20_8_13_18_1_7110 48 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 133 198 (accept_3_5 47 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 133 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 133 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 198 (accept_3_5 44 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 133 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 198 (accept_3_5 41 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 40 133 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 198 (accept_3_5 38 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 198 (Polychromatic418967fa.accept_14_9_7_2_1_2483 37 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 198 (accept_3_5 35 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 198 (Polychromatic418967fa.accept_21_13_7_9_1_2528 34 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 198
  (Polychromatic418967fa.accept_14_5_7_2_1_468 33 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 198 (accept_3_5 32 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 198 (Polychromatic418967fa.accept_23_7_18_14_1_11585 30 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 198 (accept_3_5 29 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 198 (Polychromatic418967fa.accept_20_8_13_18_1_7110 28 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 198 (accept_3_5 26 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 198 (Polychromatic418967fa.accept_15_9_13_3_1_535 24 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 198 (accept_3_5 23 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 198 (Polychromatic418967fa.accept_20_2_13_18_1_5615 22 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 21 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 198 (accept_3_5 20 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 198 (Polychromatic418967fa.accept_21_18_7_9_1_2529 18 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 198 (accept_3_5 17 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 198 (accept_3_5 14 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 198 (Polychromatic418967fa.accept_21_13_7_9_1_2528 13 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 198 (accept_3_5 11 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 133
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 198
  (Polychromatic418967fa.accept_14_9_7_2_1_2483 9 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 198 (accept_3_5 8 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 198 (accept_3_5 5 133 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 198 (Polychromatic418967fa.accept_16_4_5_6_1_8071 4 133 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 198 (accept_3_5 2 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 133 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 132 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 132 198 66 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 132 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 132 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 198 2 32 66 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 132 198 3 21 44 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 132 198 2 31 66 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 61 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 198 6 10 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 198 2 29 66 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 132 198 3 19 44 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 198 2 28 66 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 55 132 198 11 5 12 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 132 198 6 9 22 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 132 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 198 2 26 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 132 198 3 17 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 198 2 25 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 132
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 132 198 6 8 22 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 132 198
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 47 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 198 2 23 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 132 198 3 15 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 198 22 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 132 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43 132 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 198 6 7 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 198
  (Polychromatic418967fa.accept_17_7_13_11_1_2895 41 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 132 198 2 20 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 198 3 13 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 198 2 19 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 198 (Polychromatic418967fa.accept_13_11_2_3_1_883
  37 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 198 6 6 22 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 198 2 17 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 132 198 33 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 132 198 2 16 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 132 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31 132 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 198 6 5 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 198 2 14 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 132 198 3 9 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 132 198 2 13 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 132 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 25 132 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 198 6 4 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 198 22 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 132 198 3 7 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 132 198 2 10 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 198 (Polychromatic418967fa.accept_16_3_4_6_1_6798 19 132 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 198 6 3 22 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 198 2 8 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 132 198 3 5 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 132 198 2 7 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 132 198 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 132 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 198 6 2 22 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 132 198 11 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 132 198 2 5 66 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 198 3 3 44 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 198 2 4 66 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 198
  (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 132 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 198 6 1 22 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 132 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 198 2 2 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 198 3 1 44 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 198 2 1 66 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1 132 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 131 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 131 198 (accept_3_4 67 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 198 (accept_3_4 64 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 63 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 198
  (Polychromatic418967fa.accept_27_8_23_9_1_11584 62 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 131 198 (accept_3_4 61 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 131 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 198 (accept_3_4 58 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 198
  (Polychromatic418967fa.accept_13_4_1_3_1_3058 56 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 198 (accept_3_4 55 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 198 (Polychromatic418967fa.accept_13_2_1_3_1_419 54 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 198 (accept_3_4 52 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 51 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 50 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 198 (accept_3_4 49 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 198 (Polychromatic418967fa.accept_17_14_12_11_1_4063 48 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 198 (Polychromatic418967fa.accept_17_13_12_11_1_2947 47 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 198 (accept_3_4 46 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 198
  (Polychromatic418967fa.accept_13_5_1_3_1_878 44 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 198 (accept_3_4 43 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 198 (Polychromatic418967fa.accept_19_4_17_8_1_2103 42 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 198 (accept_3_4 40 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 198 (accept_3_4 37 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 198 (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 198 (accept_3_4 34 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 198 (accept_3_4 31 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 198 (Polychromatic418967fa.accept_13_4_1_3_1_3058 30 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 198 (accept_3_4 28 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 198 (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 198
  (Polychromatic418967fa.accept_25_1_6_23_1_11583 26 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 131 198 (accept_3_4 25 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 131 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 131
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 198 (accept_3_4 22 131
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3
  21 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 198
  (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 198 (accept_3_4 19 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 198 (accept_3_4 16 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 198 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 198
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 198 (accept_3_4 13 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 198 (Polychromatic418967fa.accept_21_12_5_9_1_8504 12 131 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 198 (accept_3_4 10 131 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 198
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 198 (accept_3_4 7 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 198 (Polychromatic418967fa.accept_13_6_1_3_1_1522 6 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 198 (accept_3_4 4 131 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 131 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 198
  (Polychromatic418967fa.accept_13_2_1_3_1_419 2 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 198 (accept_3_4 1 131 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 130 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 130 198 2 34 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 130 198 (Polychromatic418967fa.accept_15_7_10_3_1_2891 67 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 130 198 2 33 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 130 198 (accept_3_5 65 130 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 130 198 2 32 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 130 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 63 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 130 198 2 31 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 130 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 130 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 198 2 30 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 198 (accept_3_5 59 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 130 198 2 29 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 130 198 (Polychromatic418967fa.accept_12_9_10_6_1_872
  57 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 198 2 28 65 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 198 2 27 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 198 (accept_3_5 53 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 198 2 26 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 198 2 25 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 198
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 49 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 198 2 24 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 198 (accept_3_5 47 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 198 2 23 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 198 2 22 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 198
  (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 130 198 2 21 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 130 198 (accept_3_5 41 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 198 2 20 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 198 2 19 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 198
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 198 2 18 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 198 (accept_3_5 35 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 198 2 17 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 130 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 198 2 16 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 198
  (Polychromatic418967fa.accept_25_6_5_23_1_11582 31 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 198 2 15 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 198 (accept_3_5 29 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 198 2 14 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 130 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 198 2 13 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 198
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 25 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 198 2 12 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 198 (accept_3_5 23 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 198 2 11 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 198 2 10 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 198 2 9 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 198 (accept_3_5 17 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 198 2 8 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 198 2 7 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 130 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 198 2 6 65 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 198 (accept_3_5 11 130 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 198 2 5 65 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 198 2 4 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 198 (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 130 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 198 2 3 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 198 (accept_3_5 5 130 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 198 2 2 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 130 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 198 2 1 65 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 198 (Polychromatic418967fa.accept_16_1_2_6_1_2295 1
  130 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 129 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 129 198 3 23 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 129 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 68 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 129 198 3 22 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 129 198
  (Polychromatic418967fa.accept_15_5_9_3_1_528 65 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 198 3 21 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 62
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 129 198 3 20 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 198 3 19 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 198 3 18 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 198
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 52 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 198 3 17 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 50
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 198
  (Polychromatic418967fa.accept_21_7_3_9_1_5294 49 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 198 3 16 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 198 3 15 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 198 3 14 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 198 3 13 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 198 3 12 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 198 (Polychromatic418967fa.accept_7_6_3_2_1_461
  34 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 198 3 11 43 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 198 3 10 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 129 198 3 9 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 129 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 198 (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 129
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 198 3 8 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 198 3 7 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 129 198 3 6 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 129 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 129
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 198 3 5 43 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 198
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 198 3 4 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 129 198 3 3 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 129 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 198 3 2 43 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 129 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 198 3 1 43 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 129 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 1 129 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 129 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 128 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 128 198 2 35 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 69 128 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 128 198 2 34 64 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 128 198 (accept_3_4 67
  128 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 128 198 2 33 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 128 198
  (Polychromatic418967fa.accept_15_5_8_3_1_556 65 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 128 198 2 32 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 128 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 63 128 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 128 198 2 31 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 128 198 (accept_3_4 61 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 128 198 2 30 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 128 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540
  59 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 198 2 29 64 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 198 2 28 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 198 (accept_3_4 55 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 198 2 27 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 198 2 26 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 198 2 25 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 198 (accept_3_4 49 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 198 2 24 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 198 (Polychromatic418967fa.accept_13_8_11_3_1_3053 47 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 198 2 23 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 198 2 22 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 198 (accept_3_4 43 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 198 2 21 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 198 (Polychromatic418967fa.accept_13_2_11_3_1_873 41 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 198 2 20 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 198 2 19 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 198 (accept_3_4 37 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 198 2 18 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 198 (Polychromatic418967fa.accept_15_5_8_3_1_556 35 128 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 198 2 17 64 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 198 2 16 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 198 (accept_3_4 31 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 198 2 15 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 198 (Polychromatic418967fa.accept_24_5_8_6_1_8069 29 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 198 2 14 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 198 2 13 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 198 (accept_3_4 25 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 198 2 12 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 128 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 198 2 11 64 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 198 2 10 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 198 (accept_3_4 19 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 198 2 9 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 198 (Polychromatic418967fa.accept_21_17_2_9_1_6867 17 128 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 198 2 8 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 198 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 198 2 7 64 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 198
  (accept_3_4 13 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 198 2 6 64 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 198
  (Polychromatic418967fa.accept_15_11_8_3_1_1943 11 128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 198 2 5 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 128 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 198 2 4 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 198 (accept_3_4 7 128 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 198 2 3 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 5 128 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 198 2 2 64 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 3
  128 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 198 2 1 64 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 198 (accept_3_4 1
  128 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 127 198 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 127 198 (accept_3_5 71 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 198 (Polychromatic418967fa.accept_15_10_7_3_1_1939 70 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 198 (accept_3_5 68 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 198 (accept_3_5 65 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 64 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 198 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 198 (accept_3_5 62 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 198
  (Polychromatic418967fa.accept_17_9_8_11_1_1040 60 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 198 (accept_3_5 59 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 58 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 198 (accept_3_5 56 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 54 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 198 (accept_3_5 53 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 52 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 198 (Polychromatic418967fa.accept_20_11_7_18_1_8632 51 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 198 (accept_3_5 50 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 198 (accept_3_5 47 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 46 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 198 (accept_3_5 44 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 198 (Polychromatic418967fa.accept_17_9_8_11_1_1040 43 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 42 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 198 (accept_3_5 41 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 198 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 198 (accept_3_5 38 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 198
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 198 (accept_3_5 35 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 34 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 198 (accept_3_5 32 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 198
  (Polychromatic418967fa.accept_20_10_7_18_1_11564 30 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 127 198 (accept_3_5 29 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 127 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 28 127 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 198 (accept_3_5 26 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 198 (accept_3_5 23 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 22 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 198 (accept_3_5 20 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 198
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 18 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 198 (accept_3_5 17 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 198 (Polychromatic418967fa.accept_23_16_12_14_1_11581 16 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 198 (accept_3_5 14 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 198
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 198 (accept_3_5 11 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 10 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 198 (accept_3_5 8 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 6 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 198 (accept_3_5 5 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 127 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 198 (accept_3_5 2 127 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 126 198 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 126 198 18 4 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 126 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 71 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 198 2 35 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 126 198 3 23 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 126 198 2 34 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 126 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 67 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 198 6 11 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 65 126 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 198 2 32 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 198 9 7 14 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 198 2 31 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 198
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 61 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 198 6 10 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 59 126 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 198 2 29 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 198 3 19 42 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 198 2 28 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 198
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 198 18 3 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 126 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 198 2 26 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 198 3 17 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 198 2 25 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 198
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 49 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 126 198 6 8 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 126 198 (Polychromatic418967fa.accept_13_8_9_3_1_2213 47 126 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 198 2 23 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 198 9 5 14 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 198 2 22 63 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 198 6 7 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 198 2 20 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 198 3 13 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 198 2 19 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 198
  (Polychromatic418967fa.accept_25_12_1_23_1_11580 37 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 126 198 18 2 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 126 198 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 126 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 198 2 17 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 198 3 11 42 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 198 2 16 63 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 198
  (Polychromatic418967fa.accept_13_5_9_3_1_870 31 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 198 6 5 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 198 (Polychromatic418967fa.accept_19_10_12_8_1_10124 29 126 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 198 2 14 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 198 9 3 14 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 198 2 13 63 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 198
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 25 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 198 6 4 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 126 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 198 2 11 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 198 3 7 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 198 2 10 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 198
  (Polychromatic418967fa.accept_13_6_9_3_1_915 19 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 198 18 1 7 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 198 (Polychromatic418967fa.accept_25_17_1_23_1_11579 17 126 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 198 2 8 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 198 3 5 42 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 198 2 7 63 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 198 6 2 21 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 126 198 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 198 2 5 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 198 9 1 14 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 198 2 4 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 7
  126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 198 6 1 21 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 198
  (Polychromatic418967fa.accept_13_5_9_3_1_870 5 126 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 126 198 2 2 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 126 198 3 1 42 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 126 198 2 1 63 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 198 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 126 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 126
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 125 198 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 125 198 (accept_3_4 73 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 125 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 125 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 198 (accept_3_4 70 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 198 (Polychromatic418967fa.accept_15_9_5_3_1_554
  69 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 198
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 68 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 198 (accept_3_4 67 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 66 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 198 (Polychromatic418967fa.accept_21_2_20_9_1_2507 65 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 198 (accept_3_4 64 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 62 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 198 (accept_3_4 61 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 60 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 198 (accept_3_4 58 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 198
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 56 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 198 (accept_3_4 55 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 198 (Polychromatic418967fa.accept_15_9_5_3_1_554 54 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 198 (accept_3_4 52 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 198 (accept_3_4 49 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045 48 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 198 (accept_3_4 46 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 198
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 44 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 198 (accept_3_4 43 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 198 (Polychromatic418967fa.accept_16_9_13_6_1_2334 41 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 198 (accept_3_4 40 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 198 (accept_3_4 37 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 198 (accept_3_4 34 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 198 (accept_3_4 31 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 198 (Polychromatic418967fa.accept_17_13_6_11_1_4014 30 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 198 (accept_3_4 28 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 198
  (Polychromatic418967fa.accept_19_7_11_8_1_8743 26 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 198 (accept_3_4 25 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 198 (accept_3_4 22 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 198 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 198
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 198 (accept_3_4 19 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 198 (accept_3_4 16 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 198
  (Polychromatic418967fa.accept_21_14_20_9_1_5306 14 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 198 (accept_3_4 13 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 125 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 198 (accept_3_4 10 125 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 198 (Polychromatic418967fa.accept_13_9_8_3_1_3045
  9 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 198 (accept_3_4 7 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 198 (Polychromatic418967fa.accept_15_6_5_3_1_1988 6 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 198 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 198 (accept_3_4 4 125 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 198 (accept_3_4 1 125 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 124 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 124 198 2 37 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 124 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 73 124 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 124 198 2 36 62 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 124 198 (accept_3_5 71 124 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 124 198 2 35 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 124 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 124 198 2 34 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 124 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 124 198 2 33 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 124 198 (accept_3_5 65 124 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 124 198 2 32 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 124 198 (Polychromatic418967fa.accept_12_3_4_6_1_434
  63 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 198 2 31 62 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 198
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 61 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 124 198 2 30 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 124 198 (accept_3_5 59 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 198 2 29 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 198 2 28 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 198
  (Polychromatic418967fa.accept_19_17_10_8_1_5942 55 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 124 198 2 27 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 124 198 (accept_3_5 53 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 198 2 26 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 198 2 25 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 198 2 24 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 198 (accept_3_5 47 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 198 2 23 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 45 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 198 2 22 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 198
  (Polychromatic418967fa.accept_13_4_7_3_1_92 43 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 198 2 21 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 198 (accept_3_5 41 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 198 2 20 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 198 2 19 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 198
  (Polychromatic418967fa.accept_13_11_7_3_1_894 37 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 198 2 18 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 198 (accept_3_5 35 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 198 2 17 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 198 2 16 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 31 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 198 2 15 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 198 (accept_3_5 29 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 198 2 14 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 198 2 13 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 198 2 12 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 198 (accept_3_5 23 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 198 2 11 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 198 2 10 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 198 2 9 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 198 (accept_3_5 17 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 198 2 8 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 15 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 198 2 7 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 198 (Polychromatic418967fa.accept_25_13_24_23_1_11578 13 124 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 198 2 6 62 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 198 (accept_3_5 11
  124 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 198 2 5 62 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 198 2 4 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 198 (Polychromatic418967fa.accept_14_7_12_2_1_2502 7 124 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 198 2 3 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 198 (accept_3_5 5 124 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 198 2 2 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 124 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 198 2 1 62 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 198 (Polychromatic418967fa.accept_13_1_7_3_1_1503 1
  124 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 123 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 123 198 3 25 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 123 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 74 123 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 73 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 123 198 3 24 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 123 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 198 (Polychromatic418967fa.accept_12_10_3_6_1_882
  70 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 123 198 3 23 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 123 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 68 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 123 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467 67 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 123 198 3 22 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 64 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 123 198 3 21 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 123 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 62 123 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 198 3 20 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 198
  (Polychromatic418967fa.accept_21_17_18_9_1_9968 59 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 123 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 123 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 198 3 19 41 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 55 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 123 198 3 18 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 52 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 123 198 3 17 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 123 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 50 123 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 198 3 16 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 47 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 46 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 198 3 15 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  44 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 198
  (Polychromatic418967fa.accept_21_1_18_9_1_5290 43 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 198 3 14 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 198 (Polychromatic418967fa.accept_7_5_4_2_1_235
  40 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 198 3 13 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 198 3 12 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  35 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 34 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 198 3 11 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 32 123 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 198 (Polychromatic418967fa.accept_10_1_3_8_1_136
  31 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 198 3 10 41 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 198 3 9 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 26
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 198 3 8 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 123
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 198 3 7 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 19 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 198 3 6 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 198
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 198 3 5 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 198 3 4 41 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 198 3 3 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 123 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 198
  (Polychromatic418967fa.accept_19_7_9_8_1_7297 7 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 198 3 2 41 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 123 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 198 3 1 41 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 123 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 122 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 122 198 2 38 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 122 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 122 198 2 37 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 122 198 (accept_3_4 73 122 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 122 198 2 36 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 122 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 71 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 122 198 2 35 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 122 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 122 198 2 34 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 122 198 (accept_3_4 67 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 122 198 2 33 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 122 198 (Polychromatic418967fa.accept_10_5_2_8_1_135
  65 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 198 2 32 61 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 198 2 31 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 198 (accept_3_4 61 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 198 2 30 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 198 (Polychromatic418967fa.accept_15_14_2_3_1_1980 59 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 198 2 29 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 198 2 28 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 198 (accept_3_4 55 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 198 2 27 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 53 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 198 2 26 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 198 2 25 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 198 (accept_3_4 49 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 198 2 24 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 198 2 23 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 198 2 22 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 198 (accept_3_4 43 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 198 2 21 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 198 2 20 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 39 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 198 2 19 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 198 (accept_3_4 37 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 198 2 18 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 198 2 17 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 198 2 16 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 198 (accept_3_4 31 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 198 2 15 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 198 2 14 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 198 2 13 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 198 (accept_3_4 25 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 198 2 12 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 198 (Polychromatic418967fa.accept_20_3_2_18_1_11577 23 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 198 2 11 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 198 2 10 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 198 (accept_3_4 19 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 198 2 9 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 198 (Polychromatic418967fa.accept_20_17_2_18_1_11576 17 122 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 198 2 8 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 122 198 2 7 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 122 198 (accept_3_4 13 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  122 198 2 6 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 122 198 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 122 198 2 5 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 122 198 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 198 2 4 61 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 198 (accept_3_4 7 122 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122 198 2 3 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 122 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 122 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 198 2 2 61 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 198 2 1 61 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 198 (accept_3_4 1 122 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 121 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 77 121 198 11 7 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 121 198 (Polychromatic418967fa.accept_17_8_2_11_1_4069 76 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 121 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 121 198 (accept_3_5 74 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 121 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 73 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 121 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 72 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 198 (accept_3_5 71 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 198 (Polychromatic418967fa.accept_21_7_16_9_1_2417 70 121
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 121 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 69 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 121 198 (accept_3_5 68 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 121 198 11 6 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 121 198 (accept_3_5 65 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 121 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 64 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 121 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 198 (accept_3_5 62 121 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 198
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 61 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 121 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 198 (accept_3_5 59 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 121 198 (Polychromatic418967fa.accept_15_13_1_3_1_1972 58 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 198
  (Polychromatic418967fa.accept_20_17_1_18_1_11536 57 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 121 198 (accept_3_5 56 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 121 198 11 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 121 198 (Polychromatic418967fa.accept_17_3_2_11_1_1895 54 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 198 (accept_3_5 53 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 198 (Polychromatic418967fa.accept_19_14_7_8_1_10053 52 121
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 198 (accept_3_5 50 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 49 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 198 (Polychromatic418967fa.accept_20_8_1_18_1_7103 48 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 198 (accept_3_5 47 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 46 121
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 198
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 45 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 121 198 11 4 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 198
  (Polychromatic418967fa.accept_17_8_2_11_1_4069 42 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 198 (accept_3_5 41 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 40 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 198 (accept_3_5 38 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 198 (Polychromatic418967fa.accept_17_3_2_11_1_1895 37 121 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 198
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 198 (accept_3_5 35 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 198 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 121 198 11 3 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 121 198 (accept_3_5 32 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 198 (Polychromatic418967fa.accept_19_11_7_8_1_2110 30 121
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 198 (accept_3_5 29 121
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 198
  (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 198 (accept_3_5 26 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 121 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 198
  (Polychromatic418967fa.accept_21_3_16_9_1_8528 24 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 198 (accept_3_5 23 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  121 198 11 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 121 198 (Polychromatic418967fa.accept_14_7_9_2_1_2489 21 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 198 (accept_3_5 20 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 198 (Polychromatic418967fa.accept_14_4_9_2_1_95
  18 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 198 (accept_3_5 17
  121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 198
  (Polychromatic418967fa.accept_19_16_7_8_1_8820 16 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 198 (accept_3_5 14 121 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 121 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 198
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 12 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 11 121 198 11 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 10 121 198 (Polychromatic418967fa.accept_21_10_16_9_1_5302 10 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 198
  (Polychromatic418967fa.accept_10_9_1_8_1_755 9 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 198 (accept_3_5 8 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 198 (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 198 (accept_3_5 5 121 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 4 121 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 198 (accept_3_5 2 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 1 121 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 120 198 (Eq.refl Bool.true) (allA_succ_of_gcd 78 120 198 6 13 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 120 198
  (Polychromatic418967fa.accept_21_14_15_9_1_1339 77 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 120 198 2 38 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 75 120 198 3 25 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 120 198 2 37 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 120 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 73
  120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 198 6 12 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 71 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 198 2 35 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 120 198 3 23 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 198 2 34 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 198 (Polychromatic418967fa.accept_21_4_15_9_1_3839 67 120
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 120 198 6 11 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 120 198
  (Polychromatic418967fa.accept_21_2_15_9_1_3838 65 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 120 198 2 32 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 120 198 3 21 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 198 2 31 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 198 (Polychromatic418967fa.accept_17_10_1_11_1_2900 61 120
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 198 6 10 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 59 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 120 198 2 29 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 120 198 3 19 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 198 2 28 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 55 120 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 120 198 6 9 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 198
  (Polychromatic418967fa.accept_21_11_15_9_1_3868 53 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 120 198 2 26 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 198 3 17 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 198 2 25 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 198 (Polychromatic418967fa.accept_21_7_15_9_1_5289
  49 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 120 198 6 8 20 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 120 198
  (Polychromatic418967fa.accept_21_5_15_9_1_11534 47 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 120 198 2 23 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 198 3 15 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 198 2 22 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675
  43 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 198 6 7 20 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 120 198 2 20 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 120 198 3 13 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 198 2 19 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 198 (Polychromatic418967fa.accept_21_16_15_9_1_6893 37 120
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 198 6 6 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 120 198
  (Polychromatic418967fa.accept_19_16_6_8_1_8772 35 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 120 198 2 17 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 120 198 3 11 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 198 2 16 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 31 120 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 198 6 5 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 198
  (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 198 2 14 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 120 198 3 9 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 120 198 2 13 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 120 198 (Polychromatic418967fa.accept_17_8_1_11_1_4004 25 120 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 198 6 4 20 33 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 198
  (Polychromatic418967fa.accept_21_2_15_9_1_3838 23 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 120 198 2 11 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 120 198 3 7 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 120 198 2 10 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 120 198 (Polychromatic418967fa.accept_21_19_15_9_1_11533 19 120 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 198 6 3 20 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 198 2 8 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 198 3 5 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 198 2 7 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 120 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 120 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 198 6 2 20 33 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 198
  (Polychromatic418967fa.accept_21_11_15_9_1_3868 11 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 198 2 5 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 198 3 3 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 198 2 4 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 120 198 (Polychromatic418967fa.accept_17_7_1_11_1_1894 7 120 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 198 6 1 20 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 198
  (Polychromatic418967fa.accept_21_5_15_9_1_11534 5 120 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 120 198 2 2 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 120 198 3 1 40 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 120 198 2 1 60 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 1 120 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 119 198 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 119 198 (accept_3_4 79 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 119 198 (Polychromatic418967fa.accept_19_2_5_8_1_2081 78 119 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 119 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 119 198 (accept_3_4 76 119 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 119 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 75 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 119 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 74 119 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 198 (accept_3_4 73 119 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 119 198 (Polychromatic418967fa.accept_25_22_19_23_1_11575 72 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 71 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 119 198 (accept_3_4 70 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 119 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 68 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 119 198 (accept_3_4 67 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 119 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 66 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 119 198 (accept_3_4 64 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 119 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 63 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 119 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 62 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 119 198 (accept_3_4 61 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 119 198 (Polychromatic418967fa.accept_19_3_5_8_1_8790 60 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 119 198
  (Polychromatic418967fa.accept_19_2_5_8_1_2081 59 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 119 198 (accept_3_4 58 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 119 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 56 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 119 198 (accept_3_4 55 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 119 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 54 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 119 198 (accept_3_4 52 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 119 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 119 198 (Polychromatic418967fa.accept_13_11_2_3_1_883 50 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 119 198 (accept_3_4 49 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 119 198 (Polychromatic418967fa.accept_13_9_2_3_1_3027 48 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 119 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 47 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 119 198 (accept_3_4 46 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 119 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 44 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 119 198 (accept_3_4 43 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 119 198 (Polychromatic418967fa.accept_19_4_5_8_1_11520 42 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 119 198 (accept_3_4 40 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 119 198 (Polychromatic418967fa.accept_21_18_14_9_1_5351 39 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 119 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 38 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 119 198 (accept_3_4 37 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 119 198 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 35 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 119 198 (accept_3_4 34 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 119 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 119 198 (accept_3_4 31 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 119 198 (Polychromatic418967fa.accept_23_7_4_14_1_11574 30 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 119 198 (accept_3_4 28 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 119 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 119 198 (Polychromatic418967fa.accept_14_12_7_2_1_1663 26 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 198 (accept_3_4 25 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 198 (accept_3_4 22 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 198 (Polychromatic418967fa.accept_21_20_14_9_1_11573 20 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 198 (accept_3_4 19 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 198 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 198 (accept_3_4 16 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 198 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 198 (accept_3_4 13 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 198 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 198 (accept_3_4 10 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 198 (Polychromatic418967fa.accept_27_8_11_9_1_11572 8 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 198 (accept_3_4 7 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 198 (Polychromatic418967fa.accept_21_6_14_9_1_6854 6 119
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 198 (accept_3_4 4 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 198 (Polychromatic418967fa.accept_19_3_5_8_1_8790 3 119 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 2 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 198 (accept_3_4 1 119 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 118 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 118 198 2 40 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 118 198 (Polychromatic418967fa.accept_19_3_4_8_1_8808 79 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 118 198 2 39 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 118 198 (accept_3_5 77 118 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 118 198 2 38 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 118 198
  (Polychromatic418967fa.accept_12_3_10_6_1_442 75 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 118 198 2 37 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 118 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 73 118 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 118 198 2 36 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 118 198 (accept_3_5 71 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 118 198 2 35 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 118 198 (Polychromatic418967fa.accept_12_9_10_6_1_872
  69 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 118 198 2 34 59 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 118 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 118 198 2 33 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 118 198 (accept_3_5 65 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 118 198 2 32 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 118 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 63 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 198 2 31 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 198
  (Polychromatic418967fa.accept_15_1_13_3_1_2002 61 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 198 2 30 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 198 (accept_3_5 59 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 198 2 29 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 118 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 198 2 28 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 198
  (Polychromatic418967fa.accept_15_10_13_3_1_4816 55 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 118 198 2 27 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 118 198 (accept_3_5 53 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 198 2 26 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 198 2 25 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 198
  (Polychromatic418967fa.accept_17_15_16_11_1_4001 49 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 118 198 2 24 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 118 198 (accept_3_5 47 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 198 2 23 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 118 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 198 2 22 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 43 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 198 2 21 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 198 (accept_3_5 41 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 198 2 20 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 118 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 198 2 19 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 198
  (Polychromatic418967fa.accept_13_11_1_3_1_910 37 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 198 2 18 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 198 (accept_3_5 35 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 198 2 17 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 33 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 198 2 16 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 31 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 198 2 15 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 198 (accept_3_5 29 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 198 2 14 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 198 2 13 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 25 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 198 2 12 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 198 (accept_3_5 23 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 198 2 11 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 118 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 198 2 10 59 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 198
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 19 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 198 2 9 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 198 (accept_3_5 17 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 198 2 8 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 198 2 7 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 198 (Polychromatic418967fa.accept_19_13_4_8_1_11571 13 118 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 198 2 6 59 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 198 (accept_3_5 11
  118 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 198 2 5 59 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 198 2 4 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523 7 118 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 198 2 3 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 198 (accept_3_5 5 118 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 198 2 2 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 118 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 198 2 1 59 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 1
  118 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 117 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 117 198 9 9 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 117 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 80 117 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 79
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 117 198 3 26 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 117 198
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 77 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 117 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 76 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 198 3 25 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 74
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 73 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 198 9 8 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 117
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 117 198 3 23 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 117 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 68 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 198 3 22 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 117 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176
  65 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 198 9 7 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 117 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 62 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 198 (Polychromatic418967fa.accept_19_4_3_8_1_8788 61 117
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 198 3 20 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 198 3 19 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 198 (Polychromatic418967fa.accept_12_8_9_6_1_127
  56 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 198 9 6 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 117 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 117 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 198 3 17 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 50 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 49 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 198 3 16 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 46 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 198 9 5 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 117 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 198 3 14 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 198
  (Polychromatic418967fa.accept_20_1_17_18_1_1678 41 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 117 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 117 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 198 3 13 39 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 198 (Polychromatic418967fa.accept_15_7_12_3_1_1137 37 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 198 9 4 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 198 3 11 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 117 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 198 3 10 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 198
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 198 9 3 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 25 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 198 3 8 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 117
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 198 3 7 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 198 9 2 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17
  117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 198 3 5 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 198 (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 117
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 198 3 4 39 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 198 9 1 13 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 117 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 198 3 2 39 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 117 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 198 3 1 39 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 198
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 117 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 1 117 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 116 198 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 116 198 2 41 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 116 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 81 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 116 198 2 40 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 116 198 (accept_3_4 79 116 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 116 198 2 39 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 116 198
  (Polychromatic418967fa.accept_16_13_4_6_1_2322 77 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 116 198 2 38 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 116 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 75 116 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 116 198 2 37 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 116 198 (accept_3_4 73 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 116 198 2 36 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 116 198
  (Polychromatic418967fa.accept_17_3_14_11_1_5243 71 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 116 198 2 35 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 116 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 69 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 116 198 2 34 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 116 198 (accept_3_4 67 116 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 116 198 2 33 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 116 198
  (Polychromatic418967fa.accept_14_9_4_2_1_983 65 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 116 198 2 32 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 116 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 116 198 2 31 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 116 198 (accept_3_4 61 116 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 116 198 2 30 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 116 198
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 59 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 116 198 2 29 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 116 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 116 198 2 28 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 116 198 (accept_3_4 55 116 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 116 198 2 27 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 116 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 116 198 2 26 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 116 198 (Polychromatic418967fa.accept_12_3_8_6_1_895 51 116 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 116 198 2 25 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 116 198 (accept_3_4 49 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 116 198 2 24 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 116 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 47
  116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 198 2 23 58 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 198 2 22 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 198 (accept_3_4 43 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 198 2 21 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 116 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 198 2 20 58 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 198 2 19 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 198 (accept_3_4 37 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 198 2 18 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 198 2 17 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 198 2 16 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 198 (accept_3_4 31 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 198 2 15 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 116 198 (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 116 198 2 14 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 116 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 116 198 2 13 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 116 198 (accept_3_4 25 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 116 198 2 12 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 116 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 116 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 198 2 11 58 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 198 2 10 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 116 198 (accept_3_4 19 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 116 198 2 9 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 116 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 116 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 198 2 8 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 198 (Polychromatic418967fa.accept_12_3_8_6_1_895
  15 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 198 2 7 58 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 198
  (accept_3_4 13 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 198 2 6 58 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 198
  (Polychromatic418967fa.accept_16_11_4_6_1_4422 11 116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 198 2 5 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 116 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 198 2 4 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 198 (accept_3_4 7 116 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 198 2 3 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 116 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 198 2 2 58 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3
  116 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 198 2 1 58 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 198 (accept_3_4 1
  116 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 115 198 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 115 198 (accept_3_5 83 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 115 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 82 115 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 115 198 (accept_3_5 80 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 115 198 (Polychromatic418967fa.accept_13_1_11_3_1_901
  79 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 78 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 115 198 (accept_3_5 77 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 115 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 76 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 115 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 198 (accept_3_5 74 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 72 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 198 (accept_3_5 71 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 115 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 70 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 198 (accept_3_5 68 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 115 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 67 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 198
  (Polychromatic418967fa.accept_13_1_11_3_1_901 66 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 115 198 (accept_3_5 65 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 115 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 64 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 115 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 198 (accept_3_5 62 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 115 198
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 60 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 115 198 (accept_3_5 59 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 198 (Polychromatic418967fa.accept_15_13_10_3_1_1952 58 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 198 (accept_3_5 56 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 55 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 54 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 198 (accept_3_5 53 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 52 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 198 (Polychromatic418967fa.accept_15_6_10_3_1_2844 51 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 198 (accept_3_5 50 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 48 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 198 (accept_3_5 47 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 46 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 198 (accept_3_5 44 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 43 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 42 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 198 (accept_3_5 41 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 40 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 198 (Polychromatic418967fa.accept_15_9_10_3_1_2845 39 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 198 (accept_3_5 38 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 36 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 198 (accept_3_5 35 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 34 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 198 (accept_3_5 32 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 198 (Polychromatic418967fa.accept_13_5_11_3_1_902 31 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 198
  (Polychromatic418967fa.accept_19_11_1_8_1_10127 30 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 115 198 (accept_3_5 29 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 198 (Polychromatic418967fa.accept_13_2_11_3_1_873 28 115 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 198 (accept_3_5 26 115 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 198
  (Polychromatic418967fa.accept_15_9_10_3_1_2845 24 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 198 (accept_3_5 23 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 22 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 198 (accept_3_5 20 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 19 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 198
  (Polychromatic418967fa.accept_13_5_11_3_1_902 18 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 198 (accept_3_5 17 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 198 (Polychromatic418967fa.accept_19_16_1_8_1_3244 16 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 198 (accept_3_5 14 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 198 (accept_3_5 11 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 10 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 198 (accept_3_5 8 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 198 (accept_3_5 5 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 198 (Polychromatic418967fa.accept_16_4_3_6_1_6805 4 115 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 198 (accept_3_5 2 115 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 114 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 114 198 6 14 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 114 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 83 114
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 114 198 2 41 57 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 114 198 3 27 38 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 114 198 2 40 57
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 114 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 79 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 198 6 13 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 198 (Polychromatic418967fa.accept_23_8_22_14_1_9870 77 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 114 198 2 38 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 114 198 3 25 38 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 198 2 37 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 198
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 73 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 114 198 6 12 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 114 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 71 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 114 198 2 35 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 198 3 23 38 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 198 2 34 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 198
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 67 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 198 6 11 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 65 114 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 114 198 2 32 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 114 198 3 21 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 198 2 31 57 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 198
  (Polychromatic418967fa.accept_23_15_22_14_1_11570 61 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 114 198 6 10 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 114 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 59 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 198 2 29 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 198 3 19 38 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 198 2 28 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 198
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 55 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 198 6 9 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 53 114 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 198 2 26 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 198 3 17 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 198 2 25 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 49 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 198 6 8 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 198 (Polychromatic418967fa.accept_17_13_12_11_1_2947 47 114 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 198 2 23 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 198 3 15 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 198 2 22 57 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 198
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 43 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 198 6 7 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 114 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 198 2 20 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 198 3 13 38 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 198 2 19 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 37 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 114 198 6 6 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 114 198 (Polychromatic418967fa.accept_15_5_9_3_1_528 35 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 198 2 17 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 198 3 11 38 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 198 2 16 57 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 198
  (Polychromatic418967fa.accept_17_14_12_11_1_4063 31 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 114 198 6 5 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 114 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 198 2 14 57 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 198 3 9 38 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 198 2 13 57 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 198
  (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 198 6 4 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 198 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 114 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 198 2 11 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 198 3 7 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 198 2 10 57 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 19 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 198 6 3 19 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 198 (Polychromatic418967fa.accept_16_1_2_6_1_2295 17 114 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 198 2 8 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 198 3 5 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 198 2 7 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 198 (Polychromatic418967fa.accept_15_13_9_3_1_1949
  13 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 198 6 2 19 33
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 198
  (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 198 2 5 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 198 3 3 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 198 2 4 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 114 198 (Polychromatic418967fa.accept_13_7_10_3_1_1505 7 114 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 198 6 1 19 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 198
  (Polychromatic418967fa.accept_15_5_9_3_1_528 5 114 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 198 2 2 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 198 3 1 38 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 198 2 1 57 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 198 (Polychromatic418967fa.accept_16_1_2_6_1_2295 1 114 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 113 198
  (Eq.refl Bool.true) (allA_succ_of_accept 85 113 198 (accept_3_4 85 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 113 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 84 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 113 198 (accept_3_4 82 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 113 198 (Polychromatic418967fa.accept_10_1_3_8_1_136
  81 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 80 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 198 (accept_3_4 79 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 78 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 198 (Polychromatic418967fa.accept_13_12_9_3_1_3047 77 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 198 (accept_3_4 76 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 198
  (Polychromatic418967fa.accept_25_24_13_23_1_11569 74 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 113 198 (accept_3_4 73 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 113 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 72 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 198 (accept_3_4 70 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 198 (Polychromatic418967fa.accept_7_6_1_2_1_230
  69 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 198
  (Polychromatic418967fa.accept_19_11_18_8_1_5911 68 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 113 198 (accept_3_4 67 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 113 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 66 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 65 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 198 (accept_3_4 64 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 113 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 62 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 198 (accept_3_4 61 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 113 198 (Polychromatic418967fa.accept_13_8_9_3_1_2213 60 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 198 (accept_3_4 58 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 57 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 198 (accept_3_4 55 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 198 (Polychromatic418967fa.accept_13_2_9_3_1_2212 54 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 198
  (Polychromatic418967fa.accept_16_5_1_6_1_3367 53 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 198 (accept_3_4 52 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 198 (Polychromatic418967fa.accept_14_8_1_2_1_965 50 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 198 (accept_3_4 49 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 198 (accept_3_4 46 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 44 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 198 (accept_3_4 43 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 198 (Polychromatic418967fa.accept_15_12_8_3_1_1995 42 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 41 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 198 (accept_3_4 40 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 38 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 198 (accept_3_4 37 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 198 (accept_3_4 34 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 198 (Polychromatic418967fa.accept_13_7_9_3_1_1504 33 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 198 (Polychromatic418967fa.accept_13_6_9_3_1_915 32 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 198 (accept_3_4 31 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 198 (Polychromatic418967fa.accept_19_11_18_8_1_5911 30 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 198
  (Polychromatic418967fa.accept_19_10_18_8_1_3238 29 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 113 198 (accept_3_4 28 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 198 (accept_3_4 25 113
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 24 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 198 (accept_3_4 22 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 198 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 198 (accept_3_4 19 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 198 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 198 (accept_3_4 16 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 198
  (Polychromatic418967fa.accept_24_14_17_6_1_6139 14 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 198 (accept_3_4 13 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 198 (Polychromatic418967fa.accept_13_12_9_3_1_3047 12 113 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 198 (accept_3_4 10 113 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 198 (Polychromatic418967fa.accept_15_9_8_3_1_557 9
  113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 198
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 8 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 198 (accept_3_4 7 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 198 (accept_3_4 4 113 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 198
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 198 (accept_3_4 1 113 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 112 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 112 198 2 43 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 112 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 85 112 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 112 198 2 42 56 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 112 198 (accept_3_5 83
  112 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 112 198 2 41 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 112 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 81 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 112 198 2 40 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 112 198 (Polychromatic418967fa.accept_15_4_7_3_1_119 79 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 112 198 2 39 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 112 198 (accept_3_5 77 112 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 112 198 2 38 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 112 198 (Polychromatic418967fa.accept_10_5_2_8_1_135
  75 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 198 2 37 56 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 198
  (Polychromatic418967fa.accept_19_16_17_8_1_8762 73 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 112 198 2 36 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 112 198 (accept_3_5 71 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 112 198 2 35 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 112 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 69 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 198 2 34 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 198
  (Polychromatic418967fa.accept_19_10_17_8_1_5917 67 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 112 198 2 33 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 112 198 (accept_3_5 65 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 112 198 2 32 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 112 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 63 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 112 198 2 31 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 112 198
  (Polychromatic418967fa.accept_13_9_8_3_1_3045 61 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 112 198 2 30 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 112 198 (accept_3_5 59 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 112 198 2 29 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 112 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 57 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 198 2 28 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 55 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 198 2 27 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 198 (accept_3_5 53 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 198 2 26 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 51 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 198 2 25 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 198
  (Polychromatic418967fa.accept_15_4_7_3_1_119 49 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 198 2 24 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 198 (accept_3_5 47 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 198 2 23 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 198 2 22 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 198
  (Polychromatic418967fa.accept_25_18_12_23_1_11568 43 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 112 198 2 21 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 112 198 (accept_3_5 41 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 198 2 20 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 198 2 19 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 198
  (Polychromatic418967fa.accept_13_11_8_3_1_3016 37 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 198 2 18 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 198 (accept_3_5 35 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 198 2 17 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 33 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 198 2 16 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 198
  (Polychromatic418967fa.accept_13_5_8_3_1_1535 31 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 198 2 15 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 198 (accept_3_5 29 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 198 2 14 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 198 2 13 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 198 2 12 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 198 (accept_3_5 23 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 198 2 11 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 198 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 198 2 10 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 198
  (Polychromatic418967fa.accept_15_4_7_3_1_119 19 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 198 2 9 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 198 (accept_3_5 17 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 198 2 8 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 15 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 198 2 7 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 198 (Polychromatic418967fa.accept_21_13_7_9_1_2528 13 112 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 198 2 6 56 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 198 (accept_3_5 11 112 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 198 2 5 56 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 198
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 198 2 4 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 198 (Polychromatic418967fa.accept_13_7_8_3_1_1533 7 112 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 198 2 3 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 198 (accept_3_5 5 112 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 198 2 2 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 198 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 112 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 198 2 1 56 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 198 (Polychromatic418967fa.accept_17_1_10_11_1_2943
  1 112 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 111 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 111 198 3 29 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 111 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 86 111 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 111 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 85 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 111 198 3 28 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 111 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 83 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 111 198 (Polychromatic418967fa.accept_12_10_3_6_1_882
  82 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 198 3 27 37 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 80 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 111 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 79 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 111 198 3 26 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 77
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 76 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 198 3 25 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 74 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 198 3 24 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 71 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 111 198 (Polychromatic418967fa.accept_12_10_3_6_1_882 70 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 111 198 3 23 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 111 198 (Polychromatic418967fa.accept_12_8_3_6_1_909
  68 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 67 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 198 3 22 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 64
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 198 3 21 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 62 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 198 3 20 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 59
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 58 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 198 3 19 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 56 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 198
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 198 3 18 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 52
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 198 3 17 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 198 3 16 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 198 (Polychromatic418967fa.accept_13_8_7_3_1_430
  47 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 46 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 198 3 15 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 198 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 43
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 198 3 14 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 40 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 198 3 13 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 38
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 198 3 12 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 198 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 111 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 198
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 198 3 11 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 111 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 31
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 198 3 10 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 198 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 198 3 9 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 198 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 198 3 8 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 22 111 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 198 3 7 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 198
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 19 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 198 3 6 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 198
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 198 3 5 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 198 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 198 3 4 37 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 10 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 198 3 3 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 111 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 198
  (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 198 3 2 37 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 4 111 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 198 3 1 37 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 198
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 111 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 110 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 110 198 22 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 110 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 87 110 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 110 198 2 43 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 110 198 (accept_3_4 85 110 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 110 198 2 42 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 110 198
  (Polychromatic418967fa.accept_13_5_6_3_1_868 83 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 110 198 2 41 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 110 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 81 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 110 198 2 40 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 110 198 (accept_3_4 79 110 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 110 198 2 39 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 77 110 198 11 7 10 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 76 110 198 2 38 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 110 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 75 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 110 198 2 37 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 110 198 (accept_3_4 73 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 110 198 2 36 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 110 198 (Polychromatic418967fa.accept_25_21_10_23_1_11567 71 110 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 198 2 35 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 69 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 110 198 2 34 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 110 198 (accept_3_4 67 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 110 198 22 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 110 198 (Polychromatic418967fa.accept_17_14_8_11_1_4052 65 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 198 2 32 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 198 2 31 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 198 (accept_3_4 61 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 198 2 30 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 198 2 29 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 57 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 198 2 28 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 55 110 198 11 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 198 2 27 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 110 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 198 2 26 55 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 51 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 198 2 25 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 198 (accept_3_4 49 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 198 2 24 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 198 (Polychromatic418967fa.accept_15_2_5_3_1_552 47 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 198 2 23 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 198 22 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 110 198 (accept_3_4 43 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  110 198 2 21 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 110 198 (Polychromatic418967fa.accept_19_3_15_8_1_3232 41 110 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 198 2 20 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 39
  110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 110 198 2 19 55 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 110 198 (accept_3_4 37
  110 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 110 198 2 18 55 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 110 198
  (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 110 198 2 17 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 110 198 11 3 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 110 198 2 16 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 110 198 (accept_3_4 31 110 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 110 198 2 15 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 110 198 (Polychromatic418967fa.accept_24_5_14_6_1_6131 29 110 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 198 2 14 55 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 198
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 198 2 13 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 198 (accept_3_4 25 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 198 2 12 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 198 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 110 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 198 22 1 5 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 198 2 10 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 198 (accept_3_4 19 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 198 2 9 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 110 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 198 2 8 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 198 (Polychromatic418967fa.accept_12_3_2_6_1_138
  15 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 198 2 7 55 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 198
  (accept_3_4 13 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 198 2 6 55 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 11 110 198 11 1 10 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 10 110 198 2 5 55 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 198
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 110 198 2 4 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 110 198 (accept_3_4 7 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110
  198 2 3 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  110 198 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 110 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 110 198 2 2 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 110 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 198 2 1 55 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 198 (accept_3_4 1 110 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 109 198
  (Eq.refl Bool.true) (allA_succ_of_accept 89 109 198 (accept_3_5 89 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 109 198 (Polychromatic418967fa.accept_24_16_13_6_1_11519 88 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 87
  109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 109 198 (accept_3_5 86
  109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 109 198
  (Polychromatic418967fa.accept_19_9_14_8_1_11549 85 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 109 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 198 (accept_3_5 83 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 82 109 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 81 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 198 (accept_3_5 80 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 198 (Polychromatic418967fa.accept_19_2_14_8_1_3273 78 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 198 (accept_3_5 77 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 76 109 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 75 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 198 (accept_3_5 74 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 198 (Polychromatic418967fa.accept_13_8_5_3_1_427 73 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 198 (Polychromatic418967fa.accept_23_3_17_14_1_8181 72 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 198 (accept_3_5 71 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 198 (Polychromatic418967fa.accept_19_13_14_8_1_4490 70 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 69 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 198 (accept_3_5 68 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 198 (Polychromatic418967fa.accept_13_1_5_3_1_888 66 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 198 (accept_3_5 65 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 64 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 109 198 (accept_3_5 62 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 109 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 61 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 109 198 (Polychromatic418967fa.accept_13_8_5_3_1_427 60 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 198 (accept_3_5 59 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 198 (Polychromatic418967fa.accept_13_6_5_3_1_426 58 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 109 198
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 109 198 (accept_3_5 56 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 109 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 54 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 109 198 (accept_3_5 53 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 109 198 (Polychromatic418967fa.accept_15_7_4_3_1_1930 52 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 109 198 (accept_3_5 50 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 109 198 (Polychromatic418967fa.accept_23_3_17_14_1_8181 49 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 109 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 48 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 109 198 (accept_3_5 47 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 109 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 46 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 109 198
  (Polychromatic418967fa.accept_13_6_5_3_1_426 45 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 109 198 (accept_3_5 44 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 109 198 (Polychromatic418967fa.accept_19_4_14_8_1_4510 42 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 109 198 (accept_3_5 41 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 109 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 40 109 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 109 198 (accept_3_5 38 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 109 198 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 109 198 (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 109 198 (accept_3_5 35 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 109 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 34 109 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 198 (accept_3_5 32 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 198 (Polychromatic418967fa.accept_17_13_7_11_1_3985 30 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 198 (accept_3_5 29 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 198 (Polychromatic418967fa.accept_13_2_5_3_1_406 28 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 198 (accept_3_5 26 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 198 (Polychromatic418967fa.accept_16_9_13_6_1_2334 25 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 198 (accept_3_5 23 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 198 (Polychromatic418967fa.accept_13_9_5_3_1_428 22 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 198
  (Polychromatic418967fa.accept_10_1_9_8_1_123 21 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 198 (accept_3_5 20 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 198 (Polychromatic418967fa.accept_17_1_7_11_1_2892 18 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 198 (accept_3_5 17 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 198 (Polychromatic418967fa.accept_15_1_4_3_1_1928 16 109
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 198 (accept_3_5 14 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 198 (accept_3_5 11 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 198 (Polychromatic418967fa.accept_27_10_1_9_1_11566 10 109 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 198
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 198 (accept_3_5 8 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 198 (accept_3_5 5 109 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 198 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 109 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 198 (accept_3_5 2 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 198 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 109 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 108 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 108 198 18 5 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 108 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 89 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 108 198 2 44 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 198 3 29 36 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 108 198 2 43 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 108 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 85 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 198 6 14 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 83 108 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 198 2 41 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 198 9 9 12 22 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 198 2 40 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 198
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 79 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 198 6 13 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 198 (Polychromatic418967fa.accept_13_12_4_3_1_1528 77 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 198 2 38 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 198 3 25 36 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 198 2 37 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 198
  (Polychromatic418967fa.accept_17_5_6_11_1_3974 73 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 198 18 4 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 108 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 71 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 198 2 35 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 198 3 23 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 198 2 34 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 198
  (Polychromatic418967fa.accept_23_21_16_14_1_8180 67 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 108 198 6 11 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 108 198 (Polychromatic418967fa.accept_21_2_3_9_1_1317 65 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 198 2 32 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 198 9 7 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 198 2 31 54 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 61 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 198 6 10 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 59 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 198 2 29 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 198 3 19 36 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 198 2 28 54 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 55 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 198 18 3 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 198 (Polychromatic418967fa.accept_13_1_4_3_1_1545 53 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 198 2 26 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 198 3 17 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 198 2 25 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 198
  (Polychromatic418967fa.accept_21_7_3_9_1_5294 49 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 198 6 8 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 198 2 23 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 198 9 5 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 198 2 22 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 43 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 198 6 7 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 198 2 20 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 198 3 13 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 198 2 19 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 198
  (Polychromatic418967fa.accept_19_18_13_8_1_10099 37 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 198 18 2 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 198 (Polychromatic418967fa.accept_21_14_3_9_1_11565 35 108 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 198 2 17 54 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 198 3 11 36 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 198 2 16 54
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 198
  (Polychromatic418967fa.accept_20_11_8_18_1_7090 31 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 108 198 6 5 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 108 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 198 2 14 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 198 9 3 12 22 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 198 2 13 54 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 198
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 25 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 198 6 4 18 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 198 (Polychromatic418967fa.accept_19_4_13_8_1_11544 23 108 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 198 2 11 54 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 198 3 7 36 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 198 2 10 54 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 19 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 198 18 1 6 11 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 198 (Polychromatic418967fa.accept_21_17_3_9_1_8524 17 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 198 2 8 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 198 3 5 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 198 2 7 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 13
  108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 198 6 2 18 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 198
  (Polychromatic418967fa.accept_20_11_8_18_1_7090 11 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 198 2 5 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 198 9 1 12 22 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 198 2 4 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 108 198 (Polychromatic418967fa.accept_13_7_4_3_1_3064 7 108 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 198 6 1 18 33 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 108 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 198 2 2 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 198 3 1 36 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 198 2 1 54 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 1 108 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 107 198
  (Eq.refl Bool.true) (allA_succ_of_accept 91 107 198 (accept_3_4 91 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 107 198 (Polychromatic418967fa.accept_20_10_7_18_1_11564 90 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 89
  107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 107 198 (accept_3_4 88
  107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 107 198
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 87 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 107 198 (Polychromatic418967fa.accept_19_10_12_8_1_10124 86 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 198 (accept_3_4 85 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 84 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 198
  (Polychromatic418967fa.accept_16_3_11_6_1_4467 83 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 107 198 (accept_3_4 82 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 107 198 (Polychromatic418967fa.accept_15_5_2_3_1_4876 80 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 198 (accept_3_4 79 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 198 (Polychromatic418967fa.accept_21_15_2_9_1_9962 78 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 107 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 77 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 107 198 (accept_3_4 76 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 107 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 75 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 107 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 74 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 198 (accept_3_4 73 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 72 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 198
  (Polychromatic418967fa.accept_20_11_7_18_1_8632 71 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 107 198 (accept_3_4 70 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 107 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 68 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 198 (accept_3_4 67 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 198
  (Polychromatic418967fa.accept_16_2_11_6_1_737 66 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 198 (accept_3_4 64 107 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 107 198 (Polychromatic418967fa.accept_14_7_9_2_1_2489 63 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 198
  (Polychromatic418967fa.accept_19_5_12_8_1_7273 62 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 198 (accept_3_4 61 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 59 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 198 (accept_3_4 58 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 198
  (Polychromatic418967fa.accept_21_14_2_9_1_6864 56 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 198 (accept_3_4 55 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 198 (Polychromatic418967fa.accept_21_12_2_9_1_6866 54 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 198 (accept_3_4 52 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467 51 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 198
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 50 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 198 (accept_3_4 49 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 198 (Polychromatic418967fa.accept_19_10_12_8_1_10124 48 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 198 (Polychromatic418967fa.accept_23_1_15_14_1_11538 47 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 198 (accept_3_4 46 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 198
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 44 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 198 (accept_3_4 43 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 42 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 198 (accept_3_4 40 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 198 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 198
  (Polychromatic418967fa.accept_21_17_2_9_1_6867 38 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 198 (accept_3_4 37 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 198 (Polychromatic418967fa.accept_16_4_11_6_1_5591 36 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 35 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 198 (accept_3_4 34 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 198
  (Polychromatic418967fa.accept_14_4_9_2_1_95 32 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 198 (accept_3_4 31 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 198 (Polychromatic418967fa.accept_19_11_12_8_1_11492 30 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 198 (accept_3_4 28 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 198
  (Polychromatic418967fa.accept_19_7_12_8_1_10122 26 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 107 198 (accept_3_4 25 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 107 198 (Polychromatic418967fa.accept_17_7_5_11_1_2922 24 107 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 198 (Polychromatic418967fa.accept_17_6_5_11_1_4073 23 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 198 (accept_3_4 22 107
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3
  21 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 198
  (Polychromatic418967fa.accept_15_5_2_3_1_4876 20 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 198 (accept_3_4 19 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 198 (Polychromatic418967fa.accept_14_4_9_2_1_95 18 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 198 (accept_3_4 16 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 198 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 198
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 198 (accept_3_4 13 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 198 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 198 (Polychromatic418967fa.accept_14_11_9_2_1_6382 11 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 198 (accept_3_4 10 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 198
  (Polychromatic418967fa.accept_27_8_26_9_1_7708 8 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 198 (accept_3_4 7 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 198 (Polychromatic418967fa.accept_17_6_5_11_1_4073 6 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 198 (accept_3_4 4 107 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 198 (Polychromatic418967fa.accept_16_3_11_6_1_4467 3 107 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 198
  (Polychromatic418967fa.accept_16_2_11_6_1_737 2 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 198 (accept_3_4 1 107 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 106 198
  (Eq.refl Bool.true) (allA_succ_of_gcd 92 106 198 2 46 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 106 198 (Polychromatic418967fa.accept_17_6_4_11_1_4072 91 106
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 106 198 2 45 53 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 106 198 (accept_3_5 89
  106 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 106 198 2 44 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 106 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 87 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 106 198 2 43 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 106 198 (Polychromatic418967fa.accept_14_1_8_2_1_1675 85 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 106 198 2 42 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 106 198 (accept_3_5 83 106 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 106 198 2 41 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 106 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 81 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 106 198 2 40 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 106 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 79 106 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 106 198 2 39 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 106 198 (accept_3_5 77 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 106 198 2 38 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 106 198 (Polychromatic418967fa.accept_12_3_10_6_1_442
  75 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 198 2 37 53 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 73 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 198 2 36 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 198 (accept_3_5 71 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 198 2 35 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 106 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 198 2 34 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 198
  (Polychromatic418967fa.accept_19_10_11_8_1_10121 67 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 106 198 2 33 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 106 198 (accept_3_5 65 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 198 2 32 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 198 2 31 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 198
  (Polychromatic418967fa.accept_13_9_2_3_1_3027 61 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 198 2 30 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 198 (accept_3_5 59 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 198 2 29 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 57 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 198 2 28 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 198
  (Polychromatic418967fa.accept_7_6_1_2_1_230 55 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 198 2 27 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 198 (accept_3_5 53 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 198 2 26 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 51 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 198 2 25 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 198
  (Polychromatic418967fa.accept_13_10_2_3_1_3025 49 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 198 2 24 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 198 (accept_3_5 47 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 198 2 23 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 106 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 198 2 22 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 198
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 43 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 198 2 21 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 198 (accept_3_5 41 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 198 2 20 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 198 2 19 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 198
  (Polychromatic418967fa.accept_13_11_2_3_1_883 37 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 198 2 18 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 198 (accept_3_5 35 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 198 2 17 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 198 (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 198 2 16 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 198
  (Polychromatic418967fa.accept_7_3_1_2_1_247 31 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 198 2 15 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 198 (accept_3_5 29 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 198 2 14 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 106 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 198 2 13 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 198
  (Polychromatic418967fa.accept_13_12_2_3_1_1527 25 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 198 2 12 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 198 (accept_3_5 23 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 198 2 11 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 198 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 198 2 10 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 198
  (Polychromatic418967fa.accept_15_4_1_3_1_1922 19 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 198 2 9 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 198 (accept_3_5 17 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 198 2 8 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 198 (Polychromatic418967fa.accept_12_3_10_6_1_442 15 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 198 2 7 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 198 (Polychromatic418967fa.accept_7_6_1_2_1_230 13 106 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 198 2 6 53 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 198 (accept_3_5 11 106 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 198 2 5 53 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 198
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 198 2 4 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 198 (Polychromatic418967fa.accept_19_7_11_8_1_8743 7 106 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 198 2 3 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 198 (accept_3_5 5 106 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 198 2 2 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 198 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 106 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 198 2 1 53 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 198 (Polychromatic418967fa.accept_13_1_2_3_1_911 1
  106 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 105
  198 (Eq.refl Bool.true) (allA_succ_of_gcd 93 105 198 3 31 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 105 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 92 105 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 91 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 105 198 3 30 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 105 198 (Polychromatic418967fa.accept_13_11_1_3_1_910 89 105 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 88 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 105 198 3 29 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 86 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 198 (Polychromatic418967fa.accept_13_7_1_3_1_1523
  85 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 105 198 3 28 35 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 82 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 198 3 27 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 105 198 (Polychromatic418967fa.accept_12_8_9_6_1_127
  80 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 79 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 198 3 26 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167 77 105 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 76 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 198 3 25 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 74 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132
  73 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 198 3 24 35 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 71 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 70 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 198 3 23 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 198 (Polychromatic418967fa.accept_12_8_9_6_1_127
  68 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 67 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 198 3 22 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 198 (Polychromatic418967fa.accept_14_9_7_2_1_2483 65 105 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 64 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 105 198 3 21 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 105 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 198 (Polychromatic418967fa.accept_14_5_7_2_1_468
  61 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 198 3 20 35 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 105 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 58 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 198 3 19 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 198 (Polychromatic418967fa.accept_12_8_9_6_1_127
  56 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 105 198 3 18 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 105 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 53 105 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 52 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 105 198 3 17 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 50 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 198
  (Polychromatic418967fa.accept_19_11_10_8_1_7256 49 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 105 198 3 16 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 46 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 198 3 15 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 44 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 43
  105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 198 3 14 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 198
  (Polychromatic418967fa.accept_13_2_1_3_1_419 41 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 198 3 13 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  38 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 198
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 37 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 198 3 12 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 198
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 198 3 11 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 105 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 198 3 10 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 198
  (Polychromatic418967fa.accept_16_13_9_6_1_2306 29 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 198 3 9 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 198
  (Polychromatic418967fa.accept_24_1_9_6_1_11563 25 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 105 198 3 8 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 198 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 105
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 198 3 7 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 198
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 198 3 6 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 198 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  17 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 198
  (Polychromatic418967fa.accept_12_4_9_6_1_440 16 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 198 3 5 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 198 (Polychromatic418967fa.accept_12_2_9_6_1_439 14 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 198 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 105
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 198 3 4 35 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 198 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 198 3 3 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 198 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 105 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 198 3 2 35 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 198 (Polychromatic418967fa.accept_13_5_1_3_1_878 5 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 198 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 105 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 198 3 1 35 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 198
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 105 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 198 (Polychromatic418967fa.accept_23_1_13_14_1_11562 1 105 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 104
  198 (Eq.refl Bool.true) (allA_succ_of_gcd 94 104 198 2 47 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 104 198 (Polychromatic418967fa.accept_12_9_8_6_1_466 93 104 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 104 198 2 46 52 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 104 198 (accept_3_4 91
  104 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 104 198 2 45 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 104 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 89 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 104 198 2 44 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 104 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 87 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 104 198 2 43 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 104 198 (accept_3_4 85 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 104 198 2 42 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 104 198 (Polychromatic418967fa.accept_19_7_9_8_1_7297
  83 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 104 198 2 41 52 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 104 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 81 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 104 198 2 40 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 198 (accept_3_4 79 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 104 198 2 39 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 104 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 77 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 198 2 38 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 75 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 104 198 2 37 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 104 198 (accept_3_4 73 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 198 2 36 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 104 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 198 2 35 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 198
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 104 198 2 34 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 104 198 (accept_3_4 67 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 104 198 2 33 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 104 198 (Polychromatic418967fa.accept_21_2_20_9_1_2507 65 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 198 2 32 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 198 2 31 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 198 (accept_3_4 61 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 198 2 30 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 198 2 29 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 198
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 198 2 28 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 198 (accept_3_4 55 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 198 2 27 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 198 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 198 2 26 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 51 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 198 2 25 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 198 (accept_3_4 49 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 198 2 24 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 198 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 198 2 23 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 198
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 198 2 22 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 198 (accept_3_4 43 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 198 2 21 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 198 (Polychromatic418967fa.accept_15_11_14_3_1_1965 41 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 198 2 20 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 198 2 19 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 198 (accept_3_4 37 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 198 2 18 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 198 (Polychromatic418967fa.accept_19_16_9_8_1_11539 35 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 198 2 17 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 33 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 198 2 16 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 198 (accept_3_4 31 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 198 2 15 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 198 2 14 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 198
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 198 2 13 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 198 (accept_3_4 25 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 198 2 12 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 198 (Polychromatic418967fa.accept_19_4_9_8_1_8794 23 104 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 198 2 11 52 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 198
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 198 2 10 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 198 (accept_3_4 19 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 198 2 9 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 104 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 198 2 8 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 198 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 198 2 7 52 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 198 (accept_3_4 13
  104 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 198 2 6 52 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 198
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 198 2 5 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 198 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 104 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 198 2 4 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 198 (accept_3_4 7 104 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 198 2 3 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 198 (Polychromatic418967fa.accept_24_5_8_6_1_8069 5 104 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 198 2 2 52 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 198 (Polychromatic418967fa.accept_7_3_6_2_1_90 3
  104 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 198 2 1 52 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 198 (accept_3_4 1
  104 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 103
  198 (Eq.refl Bool.true) (allA_succ_of_accept 95 103 198 (accept_3_5 95 103 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 94 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 93
  103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 103 198 (accept_3_5 92
  103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 103 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 91 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 103 198 (Polychromatic418967fa.accept_24_18_7_6_1_11561 90 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 198 (accept_3_5 89 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 88 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 87 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 103 198 (accept_3_5 86 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 103 198 (Polychromatic418967fa.accept_15_9_13_3_1_535 84 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 198 (accept_3_5 83 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 82 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 81 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 103 198 (accept_3_5 80 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 103 198 (Polychromatic418967fa.accept_16_15_7_6_1_1453 79 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 103 198 (Polychromatic418967fa.accept_17_10_1_11_1_2900 78 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 198 (accept_3_5 77 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 76 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 103 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 75 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 103 198 (accept_3_5 74 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 103 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 198 (accept_3_5 71 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 70 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 103 198 (accept_3_5 68 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 67 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 198 (accept_3_5 65 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 198 (Polychromatic418967fa.accept_25_14_3_23_1_4173 64 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 198
  (Polychromatic418967fa.accept_14_7_5_2_1_2473 63 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 103 198 (accept_3_5 62 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 198 (accept_3_5 59 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 198 (Polychromatic418967fa.accept_17_7_1_11_1_1894 58 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 103 198 (accept_3_5 56 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 103 198 (Polychromatic418967fa.accept_10_5_3_8_1_1165 55 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 103 198 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 198 (accept_3_5 53 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 52 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 198
  (Polychromatic418967fa.accept_10_1_3_8_1_136 51 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 103 198 (accept_3_5 50 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 103 198 (Polychromatic418967fa.accept_13_9_12_3_1_907 48 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 198 (accept_3_5 47 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 46 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 103 198 (accept_3_5 44 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 103 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 43 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 103 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 42 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 198 (accept_3_5 41 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 103 198 (Polychromatic418967fa.accept_15_10_13_3_1_4816 40 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 198
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 103 198 (accept_3_5 38 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 103 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 198 (accept_3_5 35 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 198 (Polychromatic418967fa.accept_29_5_16_24_1_7229 34 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 198 (accept_3_5 32 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 31 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 198 (Polychromatic418967fa.accept_13_4_12_3_1_2999 30 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 198 (accept_3_5 29 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 198 (Polychromatic418967fa.accept_13_2_12_3_1_415 28 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 198
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 103 198 (accept_3_5 26 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 103 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 198 (accept_3_5 23 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 198 (Polychromatic418967fa.accept_13_9_12_3_1_907
  22 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 198 (accept_3_5 20 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 198 (Polychromatic418967fa.accept_25_19_3_23_1_11560 19 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 198 (accept_3_5 17 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 103
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 198
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 198 (accept_3_5 14 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 198 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 198 (accept_3_5 11 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 198 (Polychromatic418967fa.accept_7_3_5_2_1_17 10 103 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 198
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 198 (accept_3_5 8 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 198 (Polychromatic418967fa.accept_14_7_5_2_1_2473 7 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 198 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 198 (accept_3_5 5 103 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 198 (Polychromatic418967fa.accept_7_4_5_2_1_243 4 103 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 198
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 198 (accept_3_5 2 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 198 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 103 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 102
  198 (Eq.refl Bool.true) (allA_succ_of_gcd 96 102 198 6 16 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 102 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 95 102 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 102 198 2 47 51 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 198 3 31 34 66
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 92 102 198 2 46 51
  99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 102 198
  (Polychromatic418967fa.accept_19_15_7_8_1_8755 91 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 198 6 15 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 89 102 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 198 2 44 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 198 3 29 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 198 2 43 51 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 85 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 198 6 14 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 83 102 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 198 2 41 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 198 3 27 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 198 2 40 51 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 198
  (Polychromatic418967fa.accept_13_1_11_3_1_901 79 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 198 6 13 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 198 (Polychromatic418967fa.accept_15_2_12_3_1_1183 77 102 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 198 2 38 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 198 3 25 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 198 2 37 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 198
  (Polychromatic418967fa.accept_13_8_11_3_1_3053 73 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 198 6 12 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 198 (Polychromatic418967fa.accept_19_14_7_8_1_10053 71 102 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 198 2 35 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 198 3 23 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 198 2 34 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 198
  (Polychromatic418967fa.accept_13_2_11_3_1_873 67 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 198 6 11 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 102 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 198 2 32 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 198 3 21 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 198 2 31 51 99 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 61 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 198 6 10 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 59 102 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 198 2 29 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 198 3 19 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 198 2 28 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 198
  (Polychromatic418967fa.accept_7_6_4_2_1_236 55 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 198 6 9 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 198 (Polychromatic418967fa.accept_13_1_11_3_1_901 53 102 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 198 2 26 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 198 3 17 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 198 2 25 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 198
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 49 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 102 198 6 8 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 102 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 102 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 198 2 23 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 198 3 15 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 198 2 22 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 198
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 43 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 102 198 6 7 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 102 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 102 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 198 2 20 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 198 3 13 34 66 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 198 2 19 51 99
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 198
  (Polychromatic418967fa.accept_14_9_4_2_1_983 37 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 198 6 6 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 198 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 102 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 198 2 17 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 198 3 11 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 198 2 16 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 198
  (Polychromatic418967fa.accept_13_5_11_3_1_902 31 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 198 6 5 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 102 198 (Polychromatic418967fa.accept_21_8_18_9_1_5329 29 102 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 198 2 14 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 198 3 9 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 198 2 13 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 198
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 198 6 4 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 198 (Polychromatic418967fa.accept_13_10_11_3_1_1518 23 102 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 198 2 11 51 99 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 198 3 7 34 66 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 198 2 10 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 198
  (Polychromatic418967fa.accept_7_5_4_2_1_235 19 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 198 6 3 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 198 (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 102 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 198 2 8 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 198 3 5 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 198 2 7 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 198 (Polychromatic418967fa.accept_7_6_4_2_1_236 13
  102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 198 6 2 17 33 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 198
  (Polychromatic418967fa.accept_19_11_7_8_1_2110 11 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 198 2 5 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 102 198 3 3 34 66 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 102 198 2 4 51 99 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 102 198 (Polychromatic418967fa.accept_13_7_11_3_1_1540 7 102 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 198 6 1 17 33 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 198 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 102 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 198 2 2 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 198 3 1 34 66 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 198 2 1 51 99 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 198
  (Polychromatic418967fa.accept_13_1_11_3_1_901 1 102 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 198)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 98 101 198 (Eq.refl Bool.true) (allA_succ_of_accept 97 101 198 (accept_3_4 97 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 96 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 95 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 101 198 (accept_3_4 94 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 101 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 93 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 92 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 101 198 (accept_3_4 91 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 90 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 89 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 101 198 (accept_3_4 88 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 101 198 (Polychromatic418967fa.accept_21_2_17_9_1_6895 86 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 101 198 (accept_3_4 85 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 101 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 84 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 83 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 101 198 (accept_3_4 82 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 101 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 81 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 101 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 80 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 198 (accept_3_4 79 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 78 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 198
  (Polychromatic418967fa.accept_20_17_1_18_1_11536 77 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 101 198 (accept_3_4 76 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 198 (Polychromatic418967fa.accept_15_14_11_3_1_1957 74 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 198 (accept_3_4 73 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 198
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 72 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 198 (accept_3_4 70 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249
  68 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 198 (accept_3_4 67
  101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 198
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 66 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 101 198 (Polychromatic418967fa.accept_16_1_5_6_1_4435 65 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 198 (accept_3_4 64 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461
  62 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 198 (accept_3_4 61
  101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 198
  (Polychromatic418967fa.accept_19_3_6_8_1_8819 60 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 198 (accept_3_4 58 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 198
  (Polychromatic418967fa.accept_17_5_16_11_1_3998 56 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 101 198 (accept_3_4 55 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 198 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 198 (accept_3_4 52 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 50 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 198 (accept_3_4 49 101 198 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 198 (accept_3_4 46
  101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 198
  (Polychromatic418967fa.accept_13_6_10_3_1_897 45 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 101 198 (Polychromatic418967fa.accept_15_14_11_3_1_1957 44 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 198 (accept_3_4 43 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 198 (Polychromatic418967fa.accept_24_18_5_6_1_11559 42 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 198
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 198 (accept_3_4 40 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 198 (Polychromatic418967fa.accept_15_8_11_3_1_3847 38 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 198 (accept_3_4 37 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 198 (accept_3_4 34 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 198 (Polychromatic418967fa.accept_13_6_10_3_1_897 32 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 198 (accept_3_4 31 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 198 (Polychromatic418967fa.accept_27_3_20_9_1_11558 30 101
  198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 198
  (Polychromatic418967fa.accept_7_1_3_2_1_13 29 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 198 (accept_3_4 28 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 198 (accept_3_4 25 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 198 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 198 (accept_3_4 22 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 198 (Polychromatic418967fa.accept_15_6_11_3_1_1172 21 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 198 (accept_3_4 19 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 198 (Polychromatic418967fa.accept_21_18_17_9_1_6897 18 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 198
  (Polychromatic418967fa.accept_16_1_5_6_1_4435 17 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 198 (accept_3_4 16 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 198 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 198 (accept_3_4 13 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 198 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 101 198
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 198
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 198 (accept_3_4 10 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 198 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 198 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 198 (accept_3_4 7 101 198 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 198 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 198
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 198 (accept_3_4 4 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 198 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 198 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 198 (Polychromatic418967fa.accept_13_2_10_3_1_1538 2 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 198 (accept_3_4 1 101 198 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 101
  198))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_198_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


