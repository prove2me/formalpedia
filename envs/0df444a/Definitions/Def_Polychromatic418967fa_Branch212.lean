-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch212
-- name    : Polychromatic418967fa_Branch212
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:24:26.413181+00:00
-- url     : https://prove2.me/theorems/0f0d40d9-0e9d-45e3-81ee-427191ba0a4e
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch212_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_212 : allB 212 212 :=
  allB_succ' 2 211 212 (Eq.refl Bool.true) (allA_of_3_0 2 211 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  210 212 (Eq.refl Bool.true) (allA_succ_of_gcd 2 210 212 2 1 105 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 212 (accept_3_2 1 210 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 212))) (allB_succ' 4 209 212 (Eq.refl Bool.true) (allA_succ_of_accept 3 209 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 209 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 209 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 209 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 212 (accept_3_2 1 209 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 209 212)))) (allB_succ' 5 208 212 (Eq.refl Bool.true) (allA_of_3_0 5 208 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 207 212 (Eq.refl Bool.true) (allA_succ_of_accept 5 207 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 207 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 212 (accept_3_2 4 207 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 207 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 212 (Polychromatic418967fa.accept_13_2_12_4_1_943 2 207 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 212 (accept_3_2 1 207 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 207 212)))))) (allB_succ' 7 206 212 (Eq.refl Bool.true) (allA_succ_of_gcd 6 206 212 2 3
  103 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 206 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 206 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 206 212 2 2 103 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 206 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 206 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 206 212 2 1 103 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 206 212 (accept_3_2 1 206 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 206 212))))))) (allB_succ' 8 205 212 (Eq.refl Bool.true) (allA_of_3_0 8 205
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 204 212 (Eq.refl Bool.true) (allA_succ_of_gcd 8 204 212 4 2
  51 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 212
  (accept_3_2 7 204 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 212 2 3 102 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 212
  (Polychromatic418967fa.accept_13_5_9_4_1_441 5 204 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 212 4 1 51 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 204 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 204 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 212 2 1 102 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 212 (accept_3_2 1 204 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 212))))))))) (allB_succ' 10 203 212 (Eq.refl Bool.true) (allA_succ_of_accept 9 203
  212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 203 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 203 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 203 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 212 (accept_3_2 7 203 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 203 212 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 203 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 203 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 5
  203 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 212 (accept_3_2 4 203
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 212 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 203 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 203 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 212 (accept_3_2 1 203 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  212)))))))))) (allB_succ' 11 202 212 (Eq.refl Bool.true) (allA_of_3_0 11 202 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 201 212 (Eq.refl Bool.true) (allA_succ_of_accept 11 201 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 201 212 (accept_3_2 10 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  201 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 201 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 201 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 212 (accept_3_2 7 201 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 201 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 212 (accept_3_2 4 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 201 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 201 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 212 (accept_3_2 1 201 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 212)))))))))))) (allB_succ' 13 200 212 (Eq.refl Bool.true) (allA_succ_of_gcd 12 200
  212 4 3 50 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  200 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 200 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 200 212 2 5 100 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 200 212 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 200 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 212 4 2 50 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 212 (accept_3_2 7 200 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 212 2 3 100 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 200 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5
  200 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 212 4 1 50 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 3 200 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 212 2 1 100 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 212 (accept_3_2 1 200 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  212))))))))))))) (allB_succ' 14 199 212 (Eq.refl Bool.true) (allA_of_3_0 14 199 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 198 212 (Eq.refl Bool.true) (allA_succ_of_gcd 14 198 212 2 7 99 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 212 (accept_3_2 13 198 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 212 2 6 99 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 212
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 198 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 212 2 5 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 212 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 198 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 212 2 4 99 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 212 (accept_3_2 7 198 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 212 2 3 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5
  198 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 212 2 2 99 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 198 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 198 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 198 212 2 1 99 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 198 212 (accept_3_2 1 198 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198
  212))))))))))))))) (allB_succ' 16 197 212 (Eq.refl Bool.true) (allA_succ_of_accept 15 197 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 197 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 197 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 212 (accept_3_2 13 197 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 197 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 197 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 212 (Polychromatic418967fa.accept_9_2_8_5_1_228
  11 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 212 (accept_3_2 10
  197 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 197 212 (Polychromatic418967fa.accept_14_8_1_2_1_965 8 197 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 212 (accept_3_2 7 197 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 197 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 197 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 5
  197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 212 (accept_3_2 4 197
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 212 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 212 (accept_3_2 1 197 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  212)))))))))))))))) (allB_succ' 17 196 212 (Eq.refl Bool.true) (allA_of_3_0 17 196 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 195 212 (Eq.refl Bool.true) (allA_succ_of_accept 17 195 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 195 212 (accept_3_2 16 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 195 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 195 212 (Polychromatic418967fa.accept_19_14_5_3_1_859 14 195 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 212 (accept_3_2 13 195 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 195 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 212 (accept_3_2 10 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 212 (Polychromatic418967fa.accept_21_9_6_2_1_3357 9 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 195 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 212 (accept_3_2 7 195 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 195 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 212 (accept_3_2 4 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 195 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 195 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 212 (accept_3_2 1 195 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 212)))))))))))))))))) (allB_succ' 19 194 212 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 194 212 2 9 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 194 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 194 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 212 2 8 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 212 (Polychromatic418967fa.accept_11_4_7_3_1_289
  15 194 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 194 212 2 7 97 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 194 212
  (accept_3_2 13 194 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 194 212 2 6 97 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 194 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 194 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 194 212 2 5 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 194 212 (Polychromatic418967fa.accept_27_9_5_23_1_1290 9 194 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 194 212 2 4 97 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 194 212 (accept_3_2 7 194 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194 212 2 3 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 194 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5
  194 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 194 212 2 2 97 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 194 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 194 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 194 212 2 1 97 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 194 212 (accept_3_2 1 194 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  212))))))))))))))))))) (allB_succ' 20 193 212 (Eq.refl Bool.true) (allA_of_3_0 20 193 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 192 212 (Eq.refl Bool.true) (allA_succ_of_gcd 20 192 212 4 5 48 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 212 (accept_3_2 19 192 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 192 212 2 9 96 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 192 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 17 192 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 212 4 4 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 192 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 192 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 212 2 7 96 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 212 (accept_3_2 13 192 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 212 4 3 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 11 192 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 212 2 5 96 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 212
  (Polychromatic418967fa.accept_21_9_3_2_1_6363 9 192 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 212 4 2 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 212 (accept_3_2 7 192 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  212 2 3 96 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 192 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 212 4 1 48 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 192 212 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 192 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 212 2 1 96 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 212 (accept_3_2 1 192 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 212))))))))))))))))))))) (allB_succ' 22 191 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 191 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 212 (Polychromatic418967fa.accept_13_7_9_4_1_918 20 191
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 191 212 (accept_3_2 19 191
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 191 212
  (Polychromatic418967fa.accept_11_7_4_3_1_302 18 191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 191 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 212 (accept_3_2 16 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 191 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 212 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 212 (accept_3_2 13
  191 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 12 191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 191 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 212 (accept_3_2 10 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 191 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 191 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 212 (accept_3_2 7 191
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 6 191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 191 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 212 (accept_3_2 4 191 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 191 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 212 (Polychromatic418967fa.accept_12_2_11_8_1_504
  2 191 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 212 (accept_3_2 1
  191 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191 212)))))))))))))))))))))) (allB_succ' 23 190 212
  (Eq.refl Bool.true) (allA_of_3_0 23 190 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 189 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 189 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 189 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 212 (accept_3_2 22 189 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 212
  (Polychromatic418967fa.accept_25_20_14_12_1_12570 20 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 189 212 (accept_3_2 19 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 189 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 189 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 212 (accept_3_2 16 189 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 212
  (Polychromatic418967fa.accept_19_15_18_3_1_1807 15 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 212 (Polychromatic418967fa.accept_19_14_18_3_1_12569 14 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 212 (accept_3_2 13 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 189
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 212 (accept_3_2 10 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 212 (Polychromatic418967fa.accept_15_8_9_2_1_1897 8 189 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 212 (accept_3_2 7 189 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 212 (accept_3_2 4 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 212 (Polychromatic418967fa.accept_13_3_7_4_1_435 3 189 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 212 (Polychromatic418967fa.accept_19_2_18_3_1_5517 2 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 212 (accept_3_2 1 189 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 212)))))))))))))))))))))))) (allB_succ' 25 188 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 188 212 4 6 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 188 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 188 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 212 2 11 94 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 21
  188 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 212 4 5 47 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 212 (accept_3_2 19
  188 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 212 2 9 94 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 188 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 188 212 4 4 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 188 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 188 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 212 2 7 94 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 212 (accept_3_2 13 188 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 212 4 3 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 188 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 212 2 5 94 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 212
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 9 188 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 212 4 2 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 212 (accept_3_2 7 188 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  212 2 3 94 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 188 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 212 4 1 47 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 188 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 188 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 212 2 1 94 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 212 (accept_3_2 1 188 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 188 212))))))))))))))))))))))))) (allB_succ' 26 187 212 (Eq.refl Bool.true)
  (allA_of_3_0 26 187 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 186 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 186 212 2 13 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 212 (accept_3_2 25 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 212 2 12 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 212 (Polychromatic418967fa.accept_14_9_4_2_1_983 23 186 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 212 2 11 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 212 2 10 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 212 (accept_3_2 19 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 212 2 9 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 186 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 212 2 8 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 212 2 7 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 212 (accept_3_2 13 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 212 2 6 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 186 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 212 2 5 93 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 212 2 4 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 212 (accept_3_2 7 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  212 2 3 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 186 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 212 2 2 93 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 186 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 212 2 1 93 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 212 (accept_3_2 1 186 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 212))))))))))))))))))))))))))) (allB_succ' 28 185 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 185 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 212 (Polychromatic418967fa.accept_7_5_3_2_1_249
  26 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 185 212 (accept_3_2 25
  185 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 185 212
  (Polychromatic418967fa.accept_16_8_9_4_1_630 24 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 23 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 212 (accept_3_2 22 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 212 (Polychromatic418967fa.accept_7_6_3_2_1_461
  20 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 212 (accept_3_2 19
  185 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 18 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 185 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 212 (accept_3_2 16 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 185 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 185 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 212 (Polychromatic418967fa.accept_12_2_5_8_1_159
  14 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 212 (accept_3_2 13
  185 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 12 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 185 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 212 (accept_3_2 10 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 185 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 8
  185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 212 (accept_3_2 7 185
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 6 185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 185 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 212 (accept_3_2 4 185 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 185 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  185 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 212 (accept_3_2 1 185
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 212)))))))))))))))))))))))))))) (allB_succ' 29 184 212
  (Eq.refl Bool.true) (allA_of_3_0 29 184 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 183 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 183 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 212 (accept_3_2 28 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 183 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 26 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 212 (accept_3_2 25 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 212 (accept_3_2 22 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 183 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 212 (accept_3_2 19 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 212 (accept_3_2 16 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 183 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 212
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 212 (accept_3_2 13 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 212 (accept_3_2 10 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 212 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 183 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 212 (accept_3_2 7 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 212 (accept_3_2 4 183 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 183 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 212 (accept_3_2 1 183 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  212)))))))))))))))))))))))))))))) (allB_succ' 31 182 212 (Eq.refl Bool.true) (allA_succ_of_gcd 30 182 212 2 15 91 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 182 212
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 182 212 2 14 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 182 212 (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 182 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 212 2 13 91 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 212 (accept_3_2 25 182 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 182 212 2 12 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 212
  (Polychromatic418967fa.accept_12_11_2_8_1_511 23 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 182 212 2 11 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 182 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 182 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 182 212 2 10 91 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 212 (accept_3_2 19 182 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 212 2 9 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 212 2 8 91 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 15 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 212 2 7 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 212 (accept_3_2 13 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 212 2 6 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 182 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 212 2 5 91 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 212 2 4 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 212 (accept_3_2 7 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  212 2 3 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 182 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 212 2 2 91 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 182 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 212 2 1 91 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 212 (accept_3_2 1 182 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 212))))))))))))))))))))))))))))))) (allB_succ' 32 181 212
  (Eq.refl Bool.true) (allA_of_3_0 32 181 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 180 212 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 180 212 4 8 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 180 212 (accept_3_2 31 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 212 2 15 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 180 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 212 4 7 45 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 212
  (Polychromatic418967fa.accept_21_6_12_2_1_4801 27 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 212 2 13 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 212 (accept_3_2 25 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 212 4 6 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 212 (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 180 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 212 2 11 90 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 212
  (Polychromatic418967fa.accept_13_8_11_4_1_1553 21 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 212 4 5 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 180 212 (accept_3_2 19 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  180 212 2 9 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 180 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 212 4 4 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 212 (Polychromatic418967fa.accept_13_2_11_4_1_445
  15 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 212 2 7 90 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 212
  (accept_3_2 13 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 212 4 3 45 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 212 2 5 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 212 (Polychromatic418967fa.accept_21_9_12_2_1_4781 9 180 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 212 4 2 45 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 212 (accept_3_2 7 180 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 212 2 3 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 212 (Polychromatic418967fa.accept_24_5_12_20_1_3817 5 180
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 212 4 1 45 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 180 212 2 1 90 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 212 (accept_3_2 1 180 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  212))))))))))))))))))))))))))))))))) (allB_succ' 34 179 212 (Eq.refl Bool.true) (allA_succ_of_accept 33 179 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 179 212 (Polychromatic418967fa.accept_13_6_10_4_1_957 32 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 212 (accept_3_2 31 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 179 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 179 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 212 (Polychromatic418967fa.accept_9_2_8_5_1_228
  29 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 212 (accept_3_2 28
  179 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 179 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 26 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 212 (accept_3_2 25 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 179 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 179 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 212 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 212 (accept_3_2 22
  179 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 179 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 20 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 212 (accept_3_2 19 179 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 179 212 (Polychromatic418967fa.accept_13_5_10_4_1_1564 18 179 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 212
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 17 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 212 (accept_3_2 16 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 179 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 212 (accept_3_2 13 179 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 179 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 11 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 212 (accept_3_2 10 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 212 (Polychromatic418967fa.accept_13_8_10_4_1_2270 8 179 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 212 (accept_3_2 7 179 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 179 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 212 (accept_3_2 4 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 2 179 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 212 (accept_3_2 1 179 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 212)))))))))))))))))))))))))))))))))) (allB_succ' 35 178 212 (Eq.refl Bool.true)
  (allA_of_3_0 35 178 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 177 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 212 (accept_3_2 34 177 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 212 (Polychromatic418967fa.accept_15_3_12_2_1_507 33 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 212
  (Polychromatic418967fa.accept_14_4_9_2_1_95 32 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 212 (accept_3_2 31 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 212 (accept_3_2 28 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 212 (Polychromatic418967fa.accept_19_8_6_3_1_4164 27 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 212 (accept_3_2 25 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 24 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 212 (accept_3_2 22 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 20 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 212 (accept_3_2 19 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 212 (accept_3_2 16 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 15 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 212
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 212 (accept_3_2 13 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 212 (accept_3_2 10 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 212 (accept_3_2 7 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 212 (accept_3_2 4 177 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 177 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 212 (accept_3_2 1 177 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  212)))))))))))))))))))))))))))))))))))) (allB_succ' 37 176 212 (Eq.refl Bool.true) (allA_succ_of_gcd 36 176 212 4 9 44
  53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 176 212
  (Polychromatic418967fa.accept_13_9_7_4_1_953 35 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 176 212 2 17 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 176 212 (Polychromatic418967fa.accept_19_14_5_3_1_859 33 176 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 212 4 8 44 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 212 (accept_3_2 31 176 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 212 2 15 88 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 212
  (Polychromatic418967fa.accept_13_3_7_4_1_435 29 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 176 212 4 7 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 176 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 176 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 212 2 13 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 212 (accept_3_2 25 176 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 212 4 6 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 212 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 176
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 212 2 11 88 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 212 4 5 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 212 (accept_3_2 19 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  176 212 2 9 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 176 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 176 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 212 4 4 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 212 (Polychromatic418967fa.accept_14_1_8_2_1_1675
  15 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 212 2 7 88 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 212
  (accept_3_2 13 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 212 4 3 44 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 176 212 2 5 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 176 212 (Polychromatic418967fa.accept_13_9_7_4_1_953 9 176 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 212 4 2 44 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 212 (accept_3_2 7 176 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 212 2 3 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 5 176 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 212 4 1 44 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 3 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 212 2 1 88 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 212 (accept_3_2 1 176 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  212))))))))))))))))))))))))))))))))))))) (allB_succ' 38 175 212 (Eq.refl Bool.true) (allA_of_3_0 38 175 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 174 212 (Eq.refl Bool.true) (allA_succ_of_gcd 38 174 212 2 19 87 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 212
  (accept_3_2 37 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 174 212 2 18 87 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 174 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 35 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 212 2 17 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 174 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 212 2 16 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 212 (accept_3_2 31 174 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 174 212 2 15 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 174 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29
  174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 212 2 14 87 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 212 2 13 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 212 (accept_3_2 25 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 212 2 12 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 212 (Polychromatic418967fa.accept_13_10_5_4_1_3107 23 174 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 212 2 11 87 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 212 2 10 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 212 (accept_3_2 19 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 212 2 9 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 174 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 212 2 8 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 212 2 7 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 212 (accept_3_2 13 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 212 2 6 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 174 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 212 2 5 87 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 212 2 4 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 212 (accept_3_2 7 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  212 2 3 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 212 (Polychromatic418967fa.accept_25_5_24_12_1_12568 5 174 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 212 2 2 87 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 174 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 212 2 1 87 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 212 (accept_3_2 1 174 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 212))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 173
  212 (Eq.refl Bool.true) (allA_succ_of_accept 39 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 212 (accept_3_2 37 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 212 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 212 (accept_3_2 34 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 212 (accept_3_2 31 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 212 (Polychromatic418967fa.accept_17_12_3_8_1_7627 29 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 212 (accept_3_2 28 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 26 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 212 (accept_3_2 25 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 212 (Polychromatic418967fa.accept_16_7_13_4_1_1348 23 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 212 (accept_3_2 22 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 212
  (Polychromatic418967fa.accept_18_2_11_14_1_69 20 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 212 (accept_3_2 19 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 212 (accept_3_2 16 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 212 (accept_3_2 13 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 212 (accept_3_2 10 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 8 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 212 (accept_3_2 7 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 6 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 212 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 212 (accept_3_2 4 173 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 212 (accept_3_2 1 173 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  212)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 172 212 (Eq.refl Bool.true) (allA_of_3_0 41 172 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 171 212 (Eq.refl Bool.true) (allA_succ_of_accept 41 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 212 (accept_3_2 40 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 38 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 212 (accept_3_2 37 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 171 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 212 (accept_3_2 34 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 212 (Polychromatic418967fa.accept_13_6_2_4_1_923 32 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 212 (accept_3_2 31 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 212 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 171
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 212 (accept_3_2 28 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 26 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 212 (accept_3_2 25 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 212 (Polychromatic418967fa.accept_13_11_2_4_1_1590 24 171 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 212 (accept_3_2 22 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 212 (Polychromatic418967fa.accept_17_4_1_8_1_5070 21 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 20 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 212 (accept_3_2 19 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 212 (accept_3_2 16 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 212 (Polychromatic418967fa.accept_21_14_3_2_1_12567 14 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 212 (accept_3_2 13 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 171 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 212 (accept_3_2 10 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 8 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 212 (accept_3_2 7 171 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 212 (accept_3_2 4 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 171 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 212 (Polychromatic418967fa.accept_25_2_21_12_1_12566 2 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 212 (accept_3_2 1 171 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 212)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 170 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 170 212 2 21 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 212 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 170 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 212 2 20 85 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 212 2 19 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 212 (accept_3_2 37 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 212 2 18 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 170 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 212 2 17 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 212 2 16 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 212 (accept_3_2 31 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 212 2 15 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 170 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 212 2 14 85 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 212
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 212 2 13 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 212 (accept_3_2 25 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 212 2 12 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 170 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 212 2 11 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 212 2 10 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 212 (accept_3_2 19 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 212 2 9 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 170 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 212 2 8 85 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 212 2 7 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 212 (accept_3_2 13 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 212 2 6 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 170 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 212 2 5 85 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 212
  (Polychromatic418967fa.accept_19_9_18_3_1_5475 9 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 212 2 4 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 212 (accept_3_2 7 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  212 2 3 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 170 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 212 2 2 85 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 3 170 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 212 2 1 85 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 212 (accept_3_2 1 170 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 212))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  169 212 (Eq.refl Bool.true) (allA_of_3_0 44 169 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 168 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 168 212 4 11 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 212 (accept_3_2 43 168 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 168 212 2 21 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 168 212 (Polychromatic418967fa.accept_13_2_12_4_1_943 41 168 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 212 4 10 42 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 168 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 168 212 2 19 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 168 212 (accept_3_2 37 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 212 4 9 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 168 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 168 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 212 2 17 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 212 (Polychromatic418967fa.accept_13_7_12_4_1_450
  33 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 212 4 8 42 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 212
  (accept_3_2 31 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 212 2 15 84 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 29 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 212 4 7 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 168 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 168 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 212 2 13 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 212 (accept_3_2 25 168 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 212 4 6 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 168 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 212 2 11 84 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 212 4 5 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 168 212 (accept_3_2 19 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  168 212 2 9 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 168 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 212 4 4 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 212 (Polychromatic418967fa.accept_10_5_8_2_1_517
  15 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 212 2 7 84 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 212
  (accept_3_2 13 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 212 4 3 42 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 11 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 212 2 5 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 168 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 168 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 212 4 2 42 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 212 (accept_3_2 7 168 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 212 2 3 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 168 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 212 4 1 42 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 168 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 3 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 168 212 2 1 84 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 212 (accept_3_2 1 168 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  212))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 167 212 (Eq.refl Bool.true) (allA_succ_of_accept 45
  167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 212 (accept_3_2 43 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 212 (Polychromatic418967fa.accept_20_2_7_12_1_5215 42 167
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 212
  (Polychromatic418967fa.accept_13_2_11_4_1_445 41 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 212 (accept_3_2 40 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 38 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 212 (accept_3_2 37 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 212 (accept_3_2 34 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 32 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 212 (accept_3_2 31 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 212 (Polychromatic418967fa.accept_16_14_7_4_1_3243 30 167 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 212 (accept_3_2 28 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 26 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 212 (accept_3_2 25 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 167 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 212
  (Polychromatic418967fa.accept_11_1_2_3_1_688 23 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 212 (accept_3_2 22 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 212 (Polychromatic418967fa.accept_13_7_11_4_1_2247 20 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 212 (accept_3_2 19 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 167 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 17 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 212 (accept_3_2 16 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 212 (accept_3_2 13 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 12 167
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 212 (accept_3_2 10 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 8 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 212 (accept_3_2 7 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 212 (Polychromatic418967fa.accept_13_6_11_4_1_938 6 167 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 212
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 212 (accept_3_2 4 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 212 (accept_3_2 1 167 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 212)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 166 212 (Eq.refl
  Bool.true) (allA_of_3_0 47 166 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 165 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 47 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 212 (accept_3_2 46 165 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 165 212 (Polychromatic418967fa.accept_13_6_9_4_1_2288 45 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 212 (accept_3_2 43 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 165 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 165 212 (accept_3_2 40 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 212 (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 165 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 212 (accept_3_2 37 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 165 212 (Polychromatic418967fa.accept_21_15_18_2_1_6376 36 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 212 (accept_3_2 34 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 212
  (Polychromatic418967fa.accept_13_6_9_4_1_2288 32 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 212 (accept_3_2 31 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 165 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 212 (accept_3_2 28 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 26 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 212 (accept_3_2 25 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 165 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 212 (accept_3_2 22 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 212 (Polychromatic418967fa.accept_13_8_9_4_1_1552 21 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 20 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 165 212 (accept_3_2 19 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 165 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 212 (accept_3_2 16 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 212
  (Polychromatic418967fa.accept_27_14_3_23_1_12565 14 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 212 (accept_3_2 13 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 165 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 12 165 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 212 (accept_3_2 10 165 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9
  165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 8 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 212 (accept_3_2 7 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  165 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 6 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 165 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 212 (accept_3_2 4 165 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 165 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 212 (accept_3_2 1 165 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  212)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 164 212 (Eq.refl Bool.true) (allA_succ_of_gcd 48
  164 212 4 12 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 164 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 164 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 212 2 23 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 212 (Polychromatic418967fa.accept_19_7_12_3_1_4169
  45 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 164 212 4 11 41 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 164 212
  (accept_3_2 43 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 164 212 2 21 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 164 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 41 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 164 212 4 10 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 164 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 39 164 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 164 212 2 19 82 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 164 212 (accept_3_2 37 164 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 164 212 4 9 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 164 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 212 2 17 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 212 4 8 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 164 212 (accept_3_2 31 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  164 212 2 15 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 164 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 164 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 212 4 7 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 27
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 212 2 13 82 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 212 (accept_3_2 25
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 212 4 6 41 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 212
  (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 164 212 2 11 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 164 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 212 4 5 41 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 212 (accept_3_2 19 164 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 212 2 9 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 212 4 4 41 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 212 2 7 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 212 (accept_3_2 13 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 212 4 3 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 164 212 (Polychromatic418967fa.accept_13_11_8_4_1_3950 11 164 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 212 2 5 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 212 (Polychromatic418967fa.accept_13_9_8_4_1_937 9
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 212 4 2 41 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 212 (accept_3_2 7
  164 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164 212 2 3 82 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 164 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 5 164 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 164 212 4 1 41 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 164 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 164 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 212 2 1 82 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 212 (accept_3_2 1 164 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 212))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 163 212
  (Eq.refl Bool.true) (allA_of_3_0 50 163 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 162 212 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 162 212 2 25 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 162 212 (accept_3_2 49 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 212 2 24 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 212 (Polychromatic418967fa.accept_19_9_10_3_1_1738 47 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 212 2 23 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 212 2 22 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 212 (accept_3_2 43 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 212 2 21 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 162 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 212 2 20 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 212
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 212 2 19 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 212 (accept_3_2 37 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 212 2 18 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 212 (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 212 2 17 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 212 2 16 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 212 (accept_3_2 31 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 212 2 15 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 212 (Polychromatic418967fa.accept_14_1_8_2_1_1675 29 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 212 2 14 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 212 2 13 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 212 (accept_3_2 25 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 212 2 12 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 212 2 11 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 212 2 10 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 212 (accept_3_2 19 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 212 2 9 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 162 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 212 2 8 81 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 212 2 7 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 212 (accept_3_2 13 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 212 2 6 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 212 (Polychromatic418967fa.accept_13_11_6_4_1_3121 11 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 212 2 5 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 212 2 4 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 212 (accept_3_2 7 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  212 2 3 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 162 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 212 2 2 81 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 162 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 212 2 1 81 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 212 (accept_3_2 1 162 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 212)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 161 212 (Eq.refl Bool.true) (allA_succ_of_accept 51 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 212 (accept_3_2 49 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 48 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 212 (accept_3_2 46 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 212
  (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 212 (accept_3_2 43 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 212 (Polychromatic418967fa.accept_13_2_5_4_1_3926 41 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 212 (accept_3_2 40 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 212 (accept_3_2 37 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 212 (Polychromatic418967fa.accept_13_9_5_4_1_1591 35 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 212 (accept_3_2 34 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 212
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 212 (accept_3_2 31 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 212 (accept_3_2 28 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 212
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 212 (accept_3_2 25 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 23 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 212 (accept_3_2 22 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 20 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 212 (accept_3_2 19 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 212 (Polychromatic418967fa.accept_19_18_9_3_1_8430 18 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 212 (Polychromatic418967fa.accept_21_17_14_2_1_4762 17 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 212 (accept_3_2 16 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 212 (accept_3_2 13 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 12 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 212 (accept_3_2 10 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 212
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 212 (accept_3_2 7 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 6 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 212 (accept_3_2 4 161 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 212 (accept_3_2 1 161 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  212)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 160 212 (Eq.refl Bool.true) (allA_of_3_0 53 160
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 159 212 (Eq.refl Bool.true) (allA_succ_of_gcd 53 159 212
  53 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 52 159
  212 (accept_3_2 52 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 212
  (Polychromatic418967fa.accept_8_3_7_4_1_42 51 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 212 (Polychromatic418967fa.accept_19_12_7_3_1_5494 50 159 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 212 (accept_3_2 49 159 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 48 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 212 (accept_3_2 46
  159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 44 159 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 212 (accept_3_2 43 159 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 212 (accept_3_2 40 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 39 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 38 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 212 (accept_3_2 37 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 212 (Polychromatic418967fa.accept_23_13_21_5_1_12564 36 159 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 212 (accept_3_2 34 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 212 (Polychromatic418967fa.accept_13_7_3_4_1_459 33 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 32 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 212 (accept_3_2 31 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 212 (accept_3_2 28 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 26 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 212 (accept_3_2 25 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 212 (accept_3_2 22 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 20 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 212 (accept_3_2 19 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 212 (accept_3_2 16 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 212 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 212 (Polychromatic418967fa.accept_13_1_3_4_1_925 14 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 212 (accept_3_2 13 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 159 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 212 (accept_3_2 10 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 212 (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 8 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 212 (accept_3_2 7 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 159 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 212 (accept_3_2 4 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 159 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 2 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 212 (accept_3_2 1 159 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 212)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 158 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 158 212 2 27 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 158 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 158 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 212 2 26 79 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 212
  (Polychromatic418967fa.accept_11_7_4_3_1_302 51 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 212 2 25 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 212 (accept_3_2 49 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 212 2 24 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 158 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 212 2 23 79 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 212 2 22 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 212 (accept_3_2 43 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 212 2 21 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 158 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 212 2 20 79 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 212
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 39 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 212 2 19 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 212 (accept_3_2 37 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 212 2 18 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 158 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 212 2 17 79 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 33 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 212 2 16 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 212 (accept_3_2 31 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 212 2 15 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 158 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 212 2 14 79 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 27 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 212 2 13 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 212 (accept_3_2 25 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 212 2 12 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 158 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 212 2 11 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 212
  (Polychromatic418967fa.accept_15_6_8_2_1_104 21 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 212 2 10 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 212 (accept_3_2 19 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 212 2 9 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 158 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 212 2 8 79 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 15 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 212 2 7 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 212 (accept_3_2 13 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 212 2 6 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 158 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 212 2 5 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 212
  (Polychromatic418967fa.accept_14_9_4_2_1_983 9 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 212 2 4 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 212 (accept_3_2 7 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  212 2 3 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 158 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 212 2 2 79 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 212 (Polychromatic418967fa.accept_17_3_5_8_1_1687 3 158 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 212 2 1 79 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 212 (accept_3_2 1 158 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 157 212 (Eq.refl Bool.true) (allA_of_3_0 56 157 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 156 212 (Eq.refl Bool.true) (allA_succ_of_gcd 56 156 212 4 14 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 212 (accept_3_2 55 156 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 156 212 2 27 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 156 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 53
  156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 212 4 13 39 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 212 2 25 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 212 (accept_3_2 49 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 212 4 12 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 156 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 212 2 23 78 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 212
  (Polychromatic418967fa.accept_11_1_2_3_1_688 45 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 212 4 11 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 212 (accept_3_2 43 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 212 2 21 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 156 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 212 4 10 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 212
  (Polychromatic418967fa.accept_16_7_12_4_1_1347 39 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 212 2 19 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 212 (accept_3_2 37 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 212 4 9 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 156 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 212 2 17 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33
  156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 212 4 8 39 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 212 (accept_3_2 31
  156 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 212 2 15 78 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 29 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 212 4 7 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 156 212 (Polychromatic418967fa.accept_15_12_6_2_1_2760 27 156 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 212 2 13 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 212 (accept_3_2 25 156 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 212 4 6 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 156 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 212 2 11 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 212
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 212 4 5 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 212 (accept_3_2 19 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  156 212 2 9 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 17 156 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 212 4 4 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 15
  156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 212 2 7 78 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 212 (accept_3_2 13
  156 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 212 4 3 39 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 11 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 212 2 5 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 212 (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 156 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 212 4 2 39 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 212 (accept_3_2 7 156 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 212 2 3 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 212 (Polychromatic418967fa.accept_16_5_12_4_1_4325 5 156 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 212 4 1 39 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 212
  (Polychromatic418967fa.accept_16_3_12_4_1_170 3 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 212 2 1 78 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 212 (accept_3_2 1 156 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 155 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 57 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 56 155
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 155 212 (accept_3_2 55 155
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 155 212
  (Polychromatic418967fa.accept_13_2_12_4_1_943 54 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 155 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 212 (accept_3_2 52 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 212 (Polychromatic418967fa.accept_12_2_11_8_1_504
  50 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 155 212 (accept_3_2 49
  155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 155 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 48 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 155 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 212 (accept_3_2 46 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 212 (Polychromatic418967fa.accept_9_8_2_5_1_237
  44 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 155 212 (accept_3_2 43
  155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 155 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 155 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 212 (accept_3_2 40 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 212 (Polychromatic418967fa.accept_7_3_1_2_1_247
  38 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 212 (accept_3_2 37
  155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 212
  (Polychromatic418967fa.accept_14_8_1_2_1_965 36 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 155 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 212 (accept_3_2 34 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 212
  (Polychromatic418967fa.accept_22_10_1_14_1_9335 32 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 155 212 (accept_3_2 31 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 155 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 30 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 212 (Polychromatic418967fa.accept_13_3_12_4_1_110 29 155
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 212 (accept_3_2 28 155
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 155 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 26 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 212 (accept_3_2 25 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 155 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 212 (Polychromatic418967fa.accept_8_7_3_4_1_404
  23 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 212 (accept_3_2 22
  155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 212
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 155 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 20 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 212 (accept_3_2 19 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 155 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 17 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 212 (accept_3_2 16 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 212 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 155 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 212 (accept_3_2 13 155 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 12 155 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 212
  (Polychromatic418967fa.accept_13_11_12_4_1_3945 11 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 212 (accept_3_2 10 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8 155 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 212 (accept_3_2 7 155 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6
  155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 212
  (Polychromatic418967fa.accept_13_5_12_4_1_449 5 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 212 (accept_3_2 4 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 2 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 212 (accept_3_2 1 155 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 154
  212 (Eq.refl Bool.true) (allA_of_3_0 59 154 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 153 212
  (Eq.refl Bool.true) (allA_succ_of_accept 59 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 212 (accept_3_2 58 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 57 153 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 212
  (Polychromatic418967fa.accept_16_8_9_4_1_630 56 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 212 (accept_3_2 55 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 212 (accept_3_2 52 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 212 (Polychromatic418967fa.accept_10_1_3_2_1_220 51 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 50 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 212 (accept_3_2 49 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 212 (Polychromatic418967fa.accept_19_10_1_3_1_12548 48 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 212 (accept_3_2 46 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 45 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 212
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 44 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 212 (accept_3_2 43 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 212 (accept_3_2 40 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 39 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 38 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 153 212 (accept_3_2 37 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 153 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 36 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 212 (accept_3_2 34 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 33 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 32 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 212 (accept_3_2 31 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 153 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 212 (accept_3_2 28 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 212 (Polychromatic418967fa.accept_13_1_10_4_1_954 27 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 212
  (Polychromatic418967fa.accept_22_4_21_14_1_9361 26 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 153 212 (accept_3_2 25 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 153 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 24 153 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 212 (accept_3_2 22 153 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 212 (Polychromatic418967fa.accept_8_5_1_4_1_628
  21 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 212
  (Polychromatic418967fa.accept_13_7_10_4_1_919 20 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 212 (accept_3_2 19 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 18 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 212 (accept_3_2 16 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 212
  (Polychromatic418967fa.accept_13_1_10_4_1_954 14 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 153 212 (accept_3_2 13 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 153 212 (Polychromatic418967fa.accept_15_12_3_2_1_2756 12 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 212 (accept_3_2 10 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 212 (Polychromatic418967fa.accept_21_9_6_2_1_3357 9 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 8 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 212 (accept_3_2 7 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 212 (accept_3_2 4 153 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 153 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 212
  (Polychromatic418967fa.accept_19_2_1_3_1_11216 2 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 212 (accept_3_2 1 153 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 152 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 152 212 4 15 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 212 2 29 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 212 4 14 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 212 (accept_3_2 55 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 212 2 27 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 212 4 13 38 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 212 2 25 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 212 (accept_3_2 49 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 212 4 12 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 212 2 23 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 212 4 11 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 212 (accept_3_2 43 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 212 2 21 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 41 152 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 212 4 10 38 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 212 2 19 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 212 (accept_3_2 37 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 212 4 9 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 152 212 (Polychromatic418967fa.accept_14_7_12_2_1_2502 35 152 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 212 2 17 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 33
  152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 212 4 8 38 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 212 (accept_3_2 31
  152 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 212 2 15 76 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 29 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 152 212 4 7 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 152 212 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 152 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 212 2 13 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 212 (accept_3_2 25 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 212 4 6 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 212 (Polychromatic418967fa.accept_16_7_8_4_1_689 23 152 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 212 2 11 76 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 212 4 5 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 152 212 (accept_3_2 19 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  152 212 2 9 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 152 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 152 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 212 4 4 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 15
  152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 212 2 7 76 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 212 (accept_3_2 13
  152 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 212 4 3 38 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 11 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 212 2 5 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 152 212 (Polychromatic418967fa.accept_16_9_8_4_1_1354 9 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 212 4 2 38 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 212 (accept_3_2 7 152 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 212 2 3 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 212 (Polychromatic418967fa.accept_13_5_9_4_1_441 5 152 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 212 4 1 38 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 3 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 212 2 1 76 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 212 (accept_3_2 1 152 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 151 212 (Eq.refl Bool.true)
  (allA_of_3_0 62 151 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 150 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 150 212 2 31 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 212 (accept_3_2 61 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 212 2 30 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 212 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 212 2 29 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 57 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 212 2 28 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 212 (accept_3_2 55 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 212 2 27 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 53 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 212 2 26 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 51 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 212 2 25 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 212 (accept_3_2 49 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 212 2 24 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 212 2 23 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 212 2 22 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 212 (accept_3_2 43 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 212 2 21 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 212 2 20 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 39 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 212 2 19 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 212 (accept_3_2 37 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 212 2 18 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 212 2 17 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 33 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 212 2 16 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 212 (accept_3_2 31 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 212 2 15 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 212 2 14 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 27 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 212 2 13 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 212 (accept_3_2 25 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 212 2 12 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 212 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 150 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 212 2 11 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 212 2 10 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 212 (accept_3_2 19 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 212 2 9 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 17 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 212 2 8 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 15 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 212 2 7 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 212 (accept_3_2 13 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 212 2 6 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 11 150 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 212 2 5 75 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 212 2 4 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 212 (accept_3_2 7 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  212 2 3 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 150 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 212 2 2 75 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 3 150 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 212 2 1 75 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 212 (accept_3_2 1 150 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 149 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 149
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 212 (accept_3_2 61 149
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 212
  (Polychromatic418967fa.accept_14_4_9_2_1_95 60 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 149 212 (Polychromatic418967fa.accept_13_7_6_4_1_933 59 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 212 (accept_3_2 58 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 212 (Polychromatic418967fa.accept_16_8_5_4_1_674
  56 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 212 (accept_3_2 55
  149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 212
  (Polychromatic418967fa.accept_13_2_6_4_1_1593 54 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 149 212 (Polychromatic418967fa.accept_11_9_6_3_1_1668 53 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 212 (accept_3_2 52 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 212 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 212 (accept_3_2 49
  149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 212
  (Polychromatic418967fa.accept_13_9_6_4_1_2243 48 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 149 212 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 212 (accept_3_2 46 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582
  44 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 212 (accept_3_2 43
  149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 149 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 212 (accept_3_2 40 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 212 (Polychromatic418967fa.accept_12_2_5_8_1_159
  38 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 212 (accept_3_2 37
  149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 212
  (Polychromatic418967fa.accept_13_10_6_4_1_1583 36 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 149 212 (Polychromatic418967fa.accept_13_9_6_4_1_2243 35 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 212 (accept_3_2 34 149 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 212 (Polychromatic418967fa.accept_14_4_9_2_1_95
  32 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 212 (accept_3_2 31
  149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 212
  (Polychromatic418967fa.accept_11_8_6_3_1_661 30 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 149 212 (Polychromatic418967fa.accept_18_11_5_14_1_4560 29 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 212 (accept_3_2 28 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 212 (accept_3_2 25 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 212 (Polychromatic418967fa.accept_13_11_6_4_1_3121 24 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 212 (Polychromatic418967fa.accept_13_10_6_4_1_1583 23 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 212 (accept_3_2 22 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 212 (accept_3_2 19 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 18 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 212 (accept_3_2 16 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 212 (accept_3_2 13 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 212 (Polychromatic418967fa.accept_15_12_14_2_1_3794 12 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 212 (accept_3_2 10 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 212
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 212 (accept_3_2 7 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 212 (Polychromatic418967fa.accept_16_6_5_4_1_4330 6 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 212 (Polychromatic418967fa.accept_13_5_6_4_1_1582 5 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 212 (accept_3_2 4 149 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 212
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 212 (accept_3_2 1 149 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 148 212 (Eq.refl Bool.true)
  (allA_of_3_0 65 148 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 147 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 212 (accept_3_2 64 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 212 (Polychromatic418967fa.accept_9_8_3_5_1_241
  62 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 212 (accept_3_2 61
  147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 60 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 212 (accept_3_2 58 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 147 212 (Polychromatic418967fa.accept_20_17_7_12_1_6632 57 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 212 (accept_3_2 55 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 212 (accept_3_2 52 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 212
  (Polychromatic418967fa.accept_15_5_12_2_1_2820 50 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 212 (accept_3_2 49 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 147 212 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 212 (accept_3_2 46 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 212 (accept_3_2 43 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 212 (accept_3_2 40 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 147 212 (accept_3_2 37 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 147 212 (Polychromatic418967fa.accept_15_6_12_2_1_2803 36 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 212 (accept_3_2 34 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 33 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 212
  (Polychromatic418967fa.accept_22_10_15_14_1_11040 32 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 147 212 (accept_3_2 31 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 147 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 212 (accept_3_2 28 147 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 212
  (Polychromatic418967fa.accept_18_9_3_14_1_3361 27 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 26 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 212 (accept_3_2 25 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23
  147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 212 (accept_3_2 22
  147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 212
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 21 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 20 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 212 (accept_3_2 19 147 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 212 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 212 (accept_3_2 16 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 212 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 212 (accept_3_2 13 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 212 (Polychromatic418967fa.accept_14_12_7_2_1_1663 12 147
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 212 (accept_3_2 10 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 8 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 212 (accept_3_2 7 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 6 147 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 212
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 212 (accept_3_2 4 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 212 (Polychromatic418967fa.accept_15_3_12_2_1_507 3 147 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 2 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 212 (accept_3_2 1 147 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 146 212 (Eq.refl Bool.true) (allA_succ_of_gcd 66 146 212 2 33 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 146 212 (Polychromatic418967fa.accept_12_5_2_8_1_172
  65 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 212 2 32 73 106
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 212
  (Polychromatic418967fa.accept_17_12_10_8_1_5039 63 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 146 212 2 31 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 146 212 (accept_3_2 61 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 212 2 30 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 212 2 29 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 212 2 28 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 212 (accept_3_2 55 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 212 2 27 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 212 2 26 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 212 2 25 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 212 (accept_3_2 49 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 212 2 24 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 146 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 212 2 23 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 212 2 22 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 212 (accept_3_2 43 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 212 2 21 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 212 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 212 2 20 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 212 2 19 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 212 (accept_3_2 37 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 212 2 18 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 212 2 17 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 33 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 212 2 16 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 212 (accept_3_2 31 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 212 2 15 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 29 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 212 2 14 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 212
  (Polychromatic418967fa.accept_13_1_3_4_1_925 27 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 212 2 13 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 212 (accept_3_2 25 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 212 2 12 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 146 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 212 2 11 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 21 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 212 2 10 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 212 (accept_3_2 19 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 212 2 9 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 212 2 8 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 15 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 212 2 7 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 212 (accept_3_2 13 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 212 2 6 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 11 146 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 212 2 5 73 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 212
  (Polychromatic418967fa.accept_15_9_11_2_1_1882 9 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 212 2 4 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 212 (accept_3_2 7 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  212 2 3 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 146 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 212 2 2 73 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 3 146 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 212 2 1 73 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 212 (accept_3_2 1 146 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 145 212 (Eq.refl Bool.true)
  (allA_of_3_0 68 145 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 144 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 144 212 4 17 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 212 (accept_3_2 67 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 212 2 33 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 212 (Polychromatic418967fa.accept_14_9_4_2_1_983 65 144 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 212 4 16 36 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 212
  (Polychromatic418967fa.accept_28_7_4_16_1_12563 63 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 144 212 2 31 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 144 212 (accept_3_2 61 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 212 4 15 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 212 (Polychromatic418967fa.accept_19_2_11_3_1_4136 59 144 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 212 2 29 72 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 212
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 212 4 14 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 212 (accept_3_2 55 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 212 2 27 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 212 (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 144 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 212 4 13 36 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 212
  (Polychromatic418967fa.accept_14_9_4_2_1_983 51 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 144 212 2 25 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 144 212 (accept_3_2 49 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 212 4 12 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 144 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 212 2 23 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 212
  (Polychromatic418967fa.accept_21_3_18_2_1_4750 45 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 212 4 11 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 212 (accept_3_2 43 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 212 2 21 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 144 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 212 4 10 36 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 212
  (Polychromatic418967fa.accept_19_1_11_3_1_5463 39 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 212 2 19 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 212 (accept_3_2 37 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 212 4 9 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 212 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 144 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 212 2 17 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 33
  144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 212 4 8 36 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 212 (accept_3_2 31
  144 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 212 2 15 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 212
  (Polychromatic418967fa.accept_13_3_1_4_1_945 29 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 212 4 7 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 144 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 27 144 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 212 2 13 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 212 (accept_3_2 25 144 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 212 4 6 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 212 (Polychromatic418967fa.accept_13_10_1_4_1_3103 23 144
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 212 2 11 72 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 212
  (Polychromatic418967fa.accept_19_2_11_3_1_4136 21 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 212 4 5 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 212 (accept_3_2 19 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  144 212 2 9 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 212 4 4 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 212
  (Polychromatic418967fa.accept_21_15_18_2_1_6376 15 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 212 2 7 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 212 (accept_3_2 13 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 212 4 3 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 212 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 144 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 212 2 5 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 212 (Polychromatic418967fa.accept_14_9_4_2_1_983 9
  144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 212 4 2 36 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 212 (accept_3_2 7
  144 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 212 2 3 72 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 5 144 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 212 4 1 36 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 144 212 (Polychromatic418967fa.accept_13_3_1_4_1_945 3 144 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 212 2 1 72 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 212 (accept_3_2 1 144 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 144 212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 143 212 (Eq.refl Bool.true) (allA_succ_of_accept 69 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12
  69 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 68 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 143 212 (accept_3_2 67 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 143 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 66 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 143 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 212 (accept_3_2 64 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 143 212 (accept_3_2 61 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 143 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 60 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 143 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 212 (accept_3_2 58 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 56 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 212 (accept_3_2 55 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 212 (Polychromatic418967fa.accept_16_5_15_4_1_9099 53 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 212 (accept_3_2 52 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 212 (accept_3_2 49 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 47 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 212 (accept_3_2 46 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 212
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 143 212 (accept_3_2 43 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 143 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 42 143 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 41 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 212 (accept_3_2 40 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 38 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 212 (accept_3_2 37 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 212 (accept_3_2 34 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 212
  (Polychromatic418967fa.accept_19_13_10_3_1_11235 32 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 143 212 (accept_3_2 31 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 143 212 (Polychromatic418967fa.accept_9_3_8_5_1_65 30 143 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 29 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 212 (accept_3_2 28 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27
  143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 212 (accept_3_2 25 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 212 (Polychromatic418967fa.accept_9_6_8_5_1_837 24 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 212 (Polychromatic418967fa.accept_22_1_11_14_1_12562 23 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 212 (accept_3_2 22 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 212 (accept_3_2 19 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 212 (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 212 (Polychromatic418967fa.accept_26_17_13_4_1_12561 17 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 212 (accept_3_2 16 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 212 (accept_3_2 13 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 212 (accept_3_2 10 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 212 (accept_3_2 7 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 5 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 212 (accept_3_2 4 143 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 212
  (Polychromatic418967fa.accept_9_2_8_5_1_228 2 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 212 (accept_3_2 1 143 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 142 212 (Eq.refl Bool.true)
  (allA_of_3_0 71 142 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 141 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 212 (accept_3_2 70 141 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 69 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 212 (Polychromatic418967fa.accept_15_8_6_2_1_1128
  68 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 212 (accept_3_2 67
  141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 66 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 212 (accept_3_2 64 141 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 212 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 62 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 212 (accept_3_2 61 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 141 212 (Polychromatic418967fa.accept_13_8_11_4_1_1553 60 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 212 (accept_3_2 58 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 56 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 212 (accept_3_2 55 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 141 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 212 (accept_3_2 52 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 212 (Polychromatic418967fa.accept_13_12_11_4_1_3111 51 141 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 212
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 50 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 212 (accept_3_2 49 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 141 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 48 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 212 (accept_3_2 46 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 45 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 44 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 212 (accept_3_2 43 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 212 (accept_3_2 40 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 39 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 38 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 212 (accept_3_2 37 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 212 (accept_3_2 34 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 212
  (Polychromatic418967fa.accept_13_6_11_4_1_938 32 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 212 (accept_3_2 31 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 30 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 212 (accept_3_2 28 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 27 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 26 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 212 (accept_3_2 25 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 24 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 212 (accept_3_2 22 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 21 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 20 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 212 (accept_3_2 19 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 212 (accept_3_2 16 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 212 (Polychromatic418967fa.accept_13_2_11_4_1_445 15 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 212
  (Polychromatic418967fa.accept_19_14_8_3_1_6981 14 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 212 (accept_3_2 13 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 212 (Polychromatic418967fa.accept_9_3_6_5_1_63 12 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 212 (accept_3_2 10 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 212 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 212
  (Polychromatic418967fa.accept_9_8_6_5_1_513 8 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 212 (accept_3_2 7 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 6 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 212 (accept_3_2 4 141 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 141 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 212
  (Polychromatic418967fa.accept_9_2_6_5_1_227 2 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 212 (accept_3_2 1 141 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 140 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 140 212 4 18 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 140 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 212 2 35 70 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 212
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 69 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 212 4 17 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 212 (accept_3_2 67 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 212 2 33 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 212 (Polychromatic418967fa.accept_16_1_12_4_1_695 65 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 212 4 16 35 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 212
  (Polychromatic418967fa.accept_13_11_10_4_1_1565 63 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 212 2 31 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 212 (accept_3_2 61 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 212 4 15 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 212 (Polychromatic418967fa.accept_13_7_10_4_1_919 59 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 212 2 29 70 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 212
  (Polychromatic418967fa.accept_13_5_10_4_1_1564 57 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 212 4 14 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 212 (accept_3_2 55 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 212 2 27 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 212 (Polychromatic418967fa.accept_13_1_10_4_1_954 53 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 212 4 13 35 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 212
  (Polychromatic418967fa.accept_16_3_12_4_1_170 51 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 212 2 25 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 212 (accept_3_2 49 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 212 4 12 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 212 (Polychromatic418967fa.accept_13_8_10_4_1_2270 47 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 212 2 23 70 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 212
  (Polychromatic418967fa.accept_13_6_10_4_1_957 45 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 212 4 11 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 212 (accept_3_2 43 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 212 2 21 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 212 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 212 4 10 35 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 212
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 212 2 19 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 212 (accept_3_2 37 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 212 4 9 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 212 (Polychromatic418967fa.accept_16_3_12_4_1_170 35 140 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 212 2 17 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 212 (Polychromatic418967fa.accept_13_7_10_4_1_919
  33 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 212 4 8 35 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 212
  (accept_3_2 31 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 212 2 15 70 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 212
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 212 4 7 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 140 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 212 2 13 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 212 (accept_3_2 25 140 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 212 4 6 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 212 (Polychromatic418967fa.accept_16_7_12_4_1_1347 23 140
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 212 2 11 70 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 212
  (Polychromatic418967fa.accept_13_8_10_4_1_2270 21 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 212 4 5 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 212 (accept_3_2 19 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 212 2 9 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 17 140 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 212 4 4 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 212
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 140 212 2 7 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 140 212 (accept_3_2 13 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 212 4 3 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 140 212 (Polychromatic418967fa.accept_13_11_10_4_1_1565 11 140 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 212 2 5 70 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 212
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 212 4 2 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 212 (accept_3_2 7 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  212 2 3 70 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 212 (Polychromatic418967fa.accept_11_5_8_3_1_66 5 140 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 212 4 1 35 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 140 212 (Polychromatic418967fa.accept_15_3_5_2_1_2816 3 140 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 212 2 1 70 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 212 (accept_3_2 1 140 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 140
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 139 212 (Eq.refl
  Bool.true) (allA_of_3_0 74 139 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 138 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 138 212 2 37 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 212 (accept_3_2 73 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 212 2 36 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 71 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 212 2 35 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 69 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 212 2 34 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 212 (accept_3_2 67 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 212 2 33 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 65 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 212 2 32 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 212
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 212 2 31 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 212 (accept_3_2 61 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 212 2 30 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 212 2 29 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 212 2 28 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 212 (accept_3_2 55 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 212 2 27 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 212 2 26 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 51 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 212 2 25 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 212 (accept_3_2 49 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 212 2 24 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 47 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 212 2 23 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 45 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 212 2 22 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 212 (accept_3_2 43 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 212 2 21 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 212 (Polychromatic418967fa.accept_11_8_6_3_1_661 41 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 212 2 20 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 39 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 212 2 19 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 212 (accept_3_2 37 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 212 2 18 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 212 (Polychromatic418967fa.accept_9_8_3_5_1_241 35 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 212 2 17 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 33 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 212 2 16 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 212 (accept_3_2 31 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 212 2 15 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 29 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 212 2 14 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 212
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 212 2 13 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 212 (accept_3_2 25 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 212 2 12 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 212 (Polychromatic418967fa.accept_13_10_8_4_1_3098 23 138 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 212 2 11 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 212
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 212 2 10 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 212 (accept_3_2 19 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 212 2 9 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 212 2 8 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 212
  (Polychromatic418967fa.accept_9_6_3_5_1_240 15 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 212 2 7 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 212 (accept_3_2 13 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 212 2 6 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 138 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 212 2 5 69 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 212
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 212 2 4 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 212 (accept_3_2 7 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  212 2 3 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 138 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 212 2 2 69 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 3 138 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 212 2 1 69 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 212 (accept_3_2 1 138 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 137 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 212 (Polychromatic418967fa.accept_10_4_7_2_1_211
  74 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 212 (accept_3_2 73
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 212
  (Polychromatic418967fa.accept_16_8_9_4_1_630 72 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 137 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 212 (accept_3_2 70 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 212 (Polychromatic418967fa.accept_7_5_4_2_1_235
  68 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 212 (accept_3_2 67
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 66 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 137 212 (Polychromatic418967fa.accept_10_5_7_2_1_516 65 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 212 (accept_3_2 64 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 212 (Polychromatic418967fa.accept_7_6_4_2_1_236
  62 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 212 (accept_3_2 61
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 60 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 137 212 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 212 (accept_3_2 58 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 212 (Polychromatic418967fa.accept_16_8_9_4_1_630
  56 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 212 (accept_3_2 55
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 54 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 137 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 212 (accept_3_2 52 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 212 (Polychromatic418967fa.accept_12_2_5_8_1_159
  50 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 212 (accept_3_2 49
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 48 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 137 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 47 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 212 (accept_3_2 46 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 212 (Polychromatic418967fa.accept_9_8_2_5_1_237
  44 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 212 (accept_3_2 43
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 42 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 137 212 (Polychromatic418967fa.accept_7_6_4_2_1_236 41 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 212 (accept_3_2 40 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 212 (Polychromatic418967fa.accept_12_2_5_8_1_159
  38 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 212 (accept_3_2 37
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 212
  (Polychromatic418967fa.accept_13_10_7_4_1_2262 36 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 137 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 212 (accept_3_2 34 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 212 (Polychromatic418967fa.accept_13_6_7_4_1_2264
  32 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 212 (accept_3_2 31
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 30 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 137 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 212 (accept_3_2 28 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 212 (Polychromatic418967fa.accept_7_5_4_2_1_235
  26 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 212 (accept_3_2 25
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 24 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 137 212 (Polychromatic418967fa.accept_13_10_7_4_1_2262 23 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 212 (accept_3_2 22 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 212 (Polychromatic418967fa.accept_7_6_4_2_1_236
  20 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 212 (accept_3_2 19
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 212
  (Polychromatic418967fa.accept_19_18_4_3_1_4140 18 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 137 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 17 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 212 (accept_3_2 16 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 212 (Polychromatic418967fa.accept_10_4_7_2_1_211
  14 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 212 (accept_3_2 13
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 212
  (Polychromatic418967fa.accept_7_5_4_2_1_235 12 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 137 212 (Polychromatic418967fa.accept_13_11_7_4_1_1561 11 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 212 (accept_3_2 10 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 8
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 212 (accept_3_2 7 137
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 212
  (Polychromatic418967fa.accept_7_6_4_2_1_236 6 137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 137 212 (Polychromatic418967fa.accept_7_5_4_2_1_235 5 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 212 (accept_3_2 4 137 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 137 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 212 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  137 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 212 (accept_3_2 1 137
  212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 136 212 (Eq.refl
  Bool.true) (allA_of_3_0 77 136 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 135 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 212 (accept_3_2 76 135 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 212 (Polychromatic418967fa.accept_13_9_5_4_1_1591
  74 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 212 (accept_3_2 73
  135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 212
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 72 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 212 (accept_3_2 70 135 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 212 (Polychromatic418967fa.accept_19_12_2_3_1_11218 69 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 212 (accept_3_2 67 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 212 (accept_3_2 64 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 212
  (Polychromatic418967fa.accept_13_10_5_4_1_3107 62 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 212 (accept_3_2 61 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 212 (Polychromatic418967fa.accept_14_4_9_2_1_95 60 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 212 (accept_3_2 58 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 212 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 212
  (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 212 (accept_3_2 55 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 212 (accept_3_2 52 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 212
  (Polychromatic418967fa.accept_19_12_2_3_1_11218 50 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 135 212 (accept_3_2 49 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 135 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 135 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 212 (accept_3_2 46 135 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 212 (Polychromatic418967fa.accept_13_6_5_4_1_3924
  45 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 212
  (Polychromatic418967fa.accept_16_12_7_4_1_687 44 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 212 (accept_3_2 43 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 135 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 212 (accept_3_2 40 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 212 (Polychromatic418967fa.accept_14_11_9_2_1_6382 39 135 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 212 (accept_3_2 37 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 212 (Polychromatic418967fa.accept_13_10_5_4_1_3107 36 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 212 (accept_3_2 34 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 212 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 212
  (Polychromatic418967fa.accept_13_6_5_4_1_3924 32 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 212 (accept_3_2 31 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 212 (accept_3_2 28 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 212
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 212 (accept_3_2 25 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 212 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 212 (accept_3_2 22 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 212 (Polychromatic418967fa.accept_14_7_9_2_1_2489 21 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 212
  (Polychromatic418967fa.accept_19_1_2_3_1_6995 20 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 212 (accept_3_2 19 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 212 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 212 (accept_3_2 16 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 212 (Polychromatic418967fa.accept_13_2_5_4_1_3926 15 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 212
  (Polychromatic418967fa.accept_13_1_5_4_1_463 14 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 212 (accept_3_2 13 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 212 (Polychromatic418967fa.accept_13_12_5_4_1_3133 12 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 212 (accept_3_2 10 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 212 (Polychromatic418967fa.accept_13_9_5_4_1_1591 9 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 212
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 212 (accept_3_2 7 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 212 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 212 (accept_3_2 4 135 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 212 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 212
  (Polychromatic418967fa.accept_13_2_5_4_1_3926 2 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 212 (accept_3_2 1 135 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 134 212 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 134 212 2 39 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 134 212 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 134 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 212 2 38 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 75 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 212 2 37 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 212 (accept_3_2 73 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 212 2 36 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 134 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 212 2 35 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 69 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 212 2 34 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 212 (accept_3_2 67 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 212 2 33 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 65 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 212 2 32 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 212
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 134 212 2 31 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 134 212 (accept_3_2 61 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 212 2 30 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 59 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 212 2 29 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 57 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 212 2 28 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 212 (accept_3_2 55 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 212 2 27 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 212 2 26 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 51 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 212 2 25 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 212 (accept_3_2 49 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 212 2 24 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 47 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 212 2 23 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 212
  (Polychromatic418967fa.accept_7_3_1_2_1_247 45 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 212 2 22 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 212 (accept_3_2 43 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 212 2 21 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 212 (Polychromatic418967fa.accept_7_6_1_2_1_230 41 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 212 2 20 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 39 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 212 2 19 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 212 (accept_3_2 37 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 212 2 18 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 212 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 134 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 212 2 17 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 33 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 212 2 16 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 212 (accept_3_2 31 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 212 2 15 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 29 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 212 2 14 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 212
  (Polychromatic418967fa.accept_7_6_1_2_1_230 27 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 212 2 13 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 212 (accept_3_2 25 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 212 2 12 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 212 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 212 2 11 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 212
  (Polychromatic418967fa.accept_9_3_8_5_1_65 21 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 212 2 10 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 212 (accept_3_2 19 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 212 2 9 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 17 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 212 2 8 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 212
  (Polychromatic418967fa.accept_9_6_8_5_1_837 15 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 212 2 7 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 212 (accept_3_2 13 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 212 2 6 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 212 (Polychromatic418967fa.accept_9_2_8_5_1_228 11 134 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 212 2 5 67 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 212
  (Polychromatic418967fa.accept_23_9_19_5_1_4082 9 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 212 2 4 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 212 (accept_3_2 7 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  212 2 3 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 212 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 134 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 212 2 2 67 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 212 (Polychromatic418967fa.accept_7_3_1_2_1_247 3 134 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 212 2 1 67 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 212 (accept_3_2 1 134 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 133 212 (Eq.refl
  Bool.true) (allA_of_3_0 80 133 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 132 212 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 132 212 4 20 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 212 (accept_3_2 79 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 212 2 39 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 212 (Polychromatic418967fa.accept_13_12_2_4_1_3131 77 132 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 212 4 19 33 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 75 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 212 2 37 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 212 (accept_3_2 73 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 212 4 18 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 71 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 212 2 35 66 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 212
  (Polychromatic418967fa.accept_25_19_7_12_1_12560 69 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 132 212 4 17 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 132 212 (accept_3_2 67 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 212 2 33 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 65 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 212 4 16 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 212
  (Polychromatic418967fa.accept_13_11_2_4_1_1590 63 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 132 212 2 31 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 132 212 (accept_3_2 61 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 212 4 15 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 59 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 212 2 29 66 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 57 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 212 4 14 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 212 (accept_3_2 55 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 212 2 27 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 212 (Polychromatic418967fa.accept_7_4_6_2_1_451 53 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 212 4 13 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 212
  (Polychromatic418967fa.accept_13_12_2_4_1_3131 51 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 212 2 25 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 212 (accept_3_2 49 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 212 4 12 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 212 (Polychromatic418967fa.accept_9_2_6_5_1_227 47 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 212 2 23 66 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 45 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 212 4 11 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 212 (accept_3_2 43 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 212 2 21 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 212 (Polychromatic418967fa.accept_21_20_6_2_1_11048 41 132 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 212 4 10 33 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 39 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 212 2 19 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 212 (accept_3_2 37 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 212 4 9 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 212 (Polychromatic418967fa.accept_9_8_6_5_1_513 35 132 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 212 2 17 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 212 (Polychromatic418967fa.accept_15_3_12_2_1_507
  33 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 212 4 8 33 53
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 212
  (accept_3_2 31 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 212 2 15 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 212
  (Polychromatic418967fa.accept_7_1_6_2_1_18 29 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 212 4 7 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 212 (Polychromatic418967fa.accept_18_9_6_14_1_5913 27 132 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 212 2 13 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 212 (accept_3_2 25 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 212 4 6 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 212 (Polychromatic418967fa.accept_19_4_18_3_1_5553 23 132
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 212 2 11 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 212
  (Polychromatic418967fa.accept_9_3_6_5_1_63 21 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 212 4 5 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 212 (accept_3_2 19 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 212 2 9 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 212 (Polychromatic418967fa.accept_7_3_6_2_1_90 17 132 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 212 4 4 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 212 (Polychromatic418967fa.accept_7_1_6_2_1_18 15
  132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 212 2 7 66 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 212 (accept_3_2 13
  132 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 212 4 3 33 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 212
  (Polychromatic418967fa.accept_7_4_6_2_1_451 11 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 212 2 5 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 132 212 (Polychromatic418967fa.accept_18_9_6_14_1_5913 9 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 212 4 2 33 53 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 212 (accept_3_2 7 132 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 212 2 3 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 212 (Polychromatic418967fa.accept_13_5_2_4_1_3955 5 132 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 212 4 1 33 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 212
  (Polychromatic418967fa.accept_7_3_6_2_1_90 3 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 132 212 2 1 66 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 132 212 (accept_3_2 1 132 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  212))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 131 212 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 80
  131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 212 (accept_3_2 79
  131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 212
  (Polychromatic418967fa.accept_17_10_12_8_1_2748 78 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 212 (Polychromatic418967fa.accept_14_7_5_2_1_2473 77 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 212 (accept_3_2 76 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 74 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 212 (accept_3_2 73 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 212 (Polychromatic418967fa.accept_16_8_3_4_1_3233 72 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 212 (accept_3_2 70 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 212
  (Polychromatic418967fa.accept_13_3_1_4_1_945 68 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 212 (accept_3_2 67 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 66 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 212 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 212 (accept_3_2 64 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 212
  (Polychromatic418967fa.accept_11_7_10_3_1_633 62 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 212 (accept_3_2 61 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 60 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 59 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 212 (accept_3_2 58 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 212
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 212 (accept_3_2 55 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 212 (Polychromatic418967fa.accept_15_9_11_2_1_1882 54 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 53 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 212 (accept_3_2 52 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 212 (accept_3_2 49 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 212 (Polychromatic418967fa.accept_22_4_21_14_1_9361 48 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 212 (accept_3_2 46 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 212
  (Polychromatic418967fa.accept_13_5_1_4_1_3966 44 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 212 (accept_3_2 43 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 212 (Polychromatic418967fa.accept_13_3_1_4_1_945 42 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 212 (Polychromatic418967fa.accept_20_1_11_12_1_2467 41 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 212 (accept_3_2 40 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 212
  (Polychromatic418967fa.accept_7_3_5_2_1_17 38 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 212 (accept_3_2 37 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 212 (Polychromatic418967fa.accept_14_7_5_2_1_2473 35 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 212 (accept_3_2 34 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 212
  (Polychromatic418967fa.accept_7_4_5_2_1_243 32 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 212 (accept_3_2 31 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 212 (Polychromatic418967fa.accept_22_8_21_14_1_9363 30 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 212 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 212 (accept_3_2 28 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 212
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 212 (accept_3_2 25 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 24 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 212 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 212 (accept_3_2 22 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 212
  (Polychromatic418967fa.accept_15_5_11_2_1_1095 20 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 212 (accept_3_2 19 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 18 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 212 (Polychromatic418967fa.accept_7_3_5_2_1_17 17 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 212 (accept_3_2 16 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 212 (accept_3_2 13 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 212 (Polychromatic418967fa.accept_16_12_3_4_1_4317 12 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 212 (Polychromatic418967fa.accept_7_4_5_2_1_243 11 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 212 (accept_3_2 10 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 212
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 212 (accept_3_2 7 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 212 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 212 (Polychromatic418967fa.accept_13_5_1_4_1_3966 5 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 212 (accept_3_2 4 131 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 212 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 212
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 212 (accept_3_2 1 131 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 130 212 (Eq.refl
  Bool.true) (allA_of_3_0 83 130 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 129 212 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 212 (accept_3_2 82 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 212 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 212 (Polychromatic418967fa.accept_9_8_3_5_1_241
  80 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 212 (accept_3_2 79
  129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 78 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 212 (accept_3_2 76 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 75 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 212 (Polychromatic418967fa.accept_9_2_3_5_1_60 74
  129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 212 (accept_3_2 73
  129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 212
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 72 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 212 (accept_3_2 70 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 69 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 212 (Polychromatic418967fa.accept_7_5_3_2_1_249
  68 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 212 (accept_3_2 67
  129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 212
  (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 212 (accept_3_2 64 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 212 (Polychromatic418967fa.accept_13_11_12_4_1_3945 63 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 62 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 212 (accept_3_2 61 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 60 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 212 (accept_3_2 58 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 57 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 56 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 212 (accept_3_2 55 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 54 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 212 (accept_3_2 52 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 51 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 50 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 212 (accept_3_2 49 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 48 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 212 (accept_3_2 46 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 212
  (Polychromatic418967fa.accept_9_8_3_5_1_241 44 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 212 (accept_3_2 43 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 42 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 212 (accept_3_2 40 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 212 (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 38 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 212 (accept_3_2 37 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 36 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 212 (accept_3_2 34 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 33 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 212
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 32 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 129 212 (accept_3_2 31 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 129 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 129 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 212
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 212 (accept_3_2 28 129 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 212 (Polychromatic418967fa.accept_7_6_3_2_1_461
  27 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 212
  (Polychromatic418967fa.accept_7_5_3_2_1_249 26 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 212 (accept_3_2 25 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 212 (Polychromatic418967fa.accept_9_6_3_5_1_240 24 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 212 (accept_3_2 22 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 212 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 212
  (Polychromatic418967fa.accept_7_6_3_2_1_461 20 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 212 (accept_3_2 19 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 212 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 212 (accept_3_2 16 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 212 (Polychromatic418967fa.accept_7_1_3_2_1_13 15 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 212
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 212 (accept_3_2 13 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 212 (Polychromatic418967fa.accept_7_5_3_2_1_249 12 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 212 (accept_3_2 10 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 212 (Polychromatic418967fa.accept_18_9_3_14_1_3361 9 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 212
  (Polychromatic418967fa.accept_7_1_3_2_1_13 8 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 212 (accept_3_2 7 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 212 (Polychromatic418967fa.accept_7_6_3_2_1_461 6 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 212 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 212 (accept_3_2 4 129 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 212 (Polychromatic418967fa.accept_13_3_12_4_1_110 3 129 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 212
  (Polychromatic418967fa.accept_9_2_3_5_1_60 2 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 212 (accept_3_2 1 129 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 128 212
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 128 212 4 21 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 128 212 (Polychromatic418967fa.accept_18_11_2_14_1_3351 83 128
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 212 2 41 64 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 212
  (Polychromatic418967fa.accept_11_4_7_3_1_289 81 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 212 4 20 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 128 212 (accept_3_2 79 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 212 2 39 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 212 (Polychromatic418967fa.accept_13_12_11_4_1_3111 77 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 212 4 19 32 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 75 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 128 212 2 37 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 128 212 (accept_3_2 73 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 212 4 18 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 71 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 212 2 35 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 69 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 212 4 17 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 212 (accept_3_2 67 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 212 2 33 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 212 4 16 32 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 212
  (Polychromatic418967fa.accept_24_15_8_20_1_12559 63 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 128 212 2 31 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 128 212 (accept_3_2 61 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 212 4 15 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 212 (Polychromatic418967fa.accept_11_4_7_3_1_289 59 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 212 2 29 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 57 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 212 4 14 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 212 (accept_3_2 55 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 212 2 27 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 53 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 212 4 13 32 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 212
  (Polychromatic418967fa.accept_9_6_2_5_1_506 51 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 128 212 2 25 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 128 212 (accept_3_2 49 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 212 4 12 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 212 (Polychromatic418967fa.accept_13_8_11_4_1_1553 47 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 212 2 23 64 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 212
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 212 4 11 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 212 (accept_3_2 43 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 212 2 21 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 212 (Polychromatic418967fa.accept_13_2_11_4_1_445 41 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 212 4 10 32 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 212
  (Polychromatic418967fa.accept_9_3_2_5_1_234 39 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 212 2 19 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 212 (accept_3_2 37 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 212 4 9 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 212 (Polychromatic418967fa.accept_9_8_2_5_1_237 35 128 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 212 2 17 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 33
  128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 212 4 8 32 53 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 212 (accept_3_2 31
  128 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 212 2 15 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 212
  (Polychromatic418967fa.accept_18_11_2_14_1_3351 29 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 128 212 4 7 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 128 212 (Polychromatic418967fa.accept_19_8_14_3_1_4151 27 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 212 2 13 64 106 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 212 (accept_3_2 25 128 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 212 4 6 32 53 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 212
  (Polychromatic418967fa.accept_13_10_11_4_1_2248 23 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 128 212 2 11 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 128 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 21 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 212 4 5 32 53 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 212 (accept_3_2 19 128 212
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 212 2 9 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 212
  (Polychromatic418967fa.accept_9_8_2_5_1_237 17 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 212 4 4 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 212 (Polychromatic418967fa.accept_9_6_2_5_1_506 15 128 212 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 212 2 7 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 212 (accept_3_2 13 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 212 4 3 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 212 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 128
  212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 212 2 5 64 106 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 212
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 212 4 2 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 212 (accept_3_2 7 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  212 2 3 64 106 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 212 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 128 212 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 212 4 1 32 53 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 212 (Polychromatic418967fa.accept_9_3_2_5_1_234 3 128 212 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 212 2 1 64 106 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 212 (accept_3_2 1 128 212 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 128
  212)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_212_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


