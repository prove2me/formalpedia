-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch206
-- name    : Polychromatic418967fa_Branch206
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:31.876858+00:00
-- url     : https://prove2.me/theorems/f95a8e10-3e6d-435f-96bc-251b107bd0e5
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch206_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_206 : allB 206 206 :=
  allB_succ' 2 205 206 (Eq.refl Bool.true) (allA_of_3_0 2 205 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  204 206 (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 206 2 1 102 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 206 (accept_3_2 1 204 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 204 206))) (allB_succ' 4 203 206 (Eq.refl Bool.true) (allA_succ_of_accept 3 203 206
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 203 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 206 (accept_3_2 1 203 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 203 206)))) (allB_succ' 5 202 206 (Eq.refl Bool.true) (allA_of_3_0 5 202 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 201 206 (Eq.refl Bool.true) (allA_succ_of_accept 5 201 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 201 206 (accept_3_2 4 201 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  201 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 201 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 201 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 206 (accept_3_2 1 201 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 201 206)))))) (allB_succ' 7 200 206 (Eq.refl Bool.true) (allA_succ_of_gcd 6 200 206 2 3
  100 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 200 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 200 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 200 206 2 2 100 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 200 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 200 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 200 206 2 1 100 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 200 206 (accept_3_2 1 200 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 200 206))))))) (allB_succ' 8 199 206 (Eq.refl Bool.true) (allA_of_3_0 8 199
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 198 206 (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 206 2 4
  99 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 206
  (accept_3_2 7 198 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 206 2 3 99 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 206
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 198 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 206 2 2 99 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 198 206 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 198 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 206 2 1 99 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 206 (accept_3_2 1 198 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198 206))))))))) (allB_succ' 10 197 206 (Eq.refl Bool.true) (allA_succ_of_accept 9 197
  206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 197 206 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 197 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 206 (accept_3_2 7 197 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 197 206 (Polychromatic418967fa.accept_15_6_2_11_1_325 6 197 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  197 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 206 (accept_3_2 4 197
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 206 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 197 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 197 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 206 (accept_3_2 1 197 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  206)))))))))) (allB_succ' 11 196 206 (Eq.refl Bool.true) (allA_of_3_0 11 196 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 195 206 (Eq.refl Bool.true) (allA_succ_of_accept 11 195 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 195 206 (accept_3_2 10 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  195 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 195 206 (Polychromatic418967fa.accept_19_8_5_16_1_2589 8 195 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 206 (accept_3_2 7 195 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 195 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 206 (accept_3_2 4 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  195 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 195 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 195 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 206 (accept_3_2 1 195 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 195 206)))))))))))) (allB_succ' 13 194 206 (Eq.refl Bool.true) (allA_succ_of_gcd 12 194
  206 2 6 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  194 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 194 206 2 5 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 194 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 194 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 194 206 2 4 97 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 194 206 (accept_3_2 7 194 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194 206 2 3 97 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 194 206
  (Polychromatic418967fa.accept_10_5_4_6_1_319 5 194 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 194 206 2 2 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 194 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 194 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 206 2 1 97 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 206 (accept_3_2 1 194 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 206))))))))))))) (allB_succ' 14 193 206 (Eq.refl Bool.true) (allA_of_3_0 14 193 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 15 192 206 (Eq.refl Bool.true) (allA_succ_of_gcd 14 192 206 2 7
  96 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 206
  (accept_3_2 13 192 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 206 2 6 96 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 206
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 206 2 5 96 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 192 206 (Polychromatic418967fa.accept_21_9_3_17_1_4365 9 192 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 206 2 4 96 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 206 (accept_3_2 7 192 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 206 2 3 96 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 5
  192 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 206 2 2 96 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 192 206
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 192 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 192 206 2 1 96 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 206 (accept_3_2 1 192 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192
  206))))))))))))))) (allB_succ' 16 191 206 (Eq.refl Bool.true) (allA_succ_of_accept 15 191 206
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 191 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 206 (accept_3_2 13 191 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 191 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 191 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 206
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 191 206 (accept_3_2 10 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 191 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 191 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 206 (accept_3_2 7 191 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 191 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 6
  191 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 191 206 (accept_3_2 4 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  191 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 191 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 191 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 206 (accept_3_2 1 191 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 206)))))))))))))))) (allB_succ' 17 190 206 (Eq.refl Bool.true) (allA_of_3_0 17 190
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 189 206 (Eq.refl Bool.true) (allA_succ_of_accept 17 189
  206 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 206 (accept_3_2 16 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 206 (Polychromatic418967fa.accept_13_1_7_11_1_702 14 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 206 (accept_3_2 13 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 206 (Polychromatic418967fa.accept_13_12_7_11_1_1935 12 189
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 206 (accept_3_2 10 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 206 (Polychromatic418967fa.accept_13_9_7_11_1_1292 9 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 206 (Polychromatic418967fa.accept_19_8_18_16_1_7937 8 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 206 (accept_3_2 7 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 206 (accept_3_2 4 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 206 (Polychromatic418967fa.accept_15_2_9_11_1_1551 2 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 206 (accept_3_2 1 189 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 206)))))))))))))))))) (allB_succ' 19 188 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 188 206 2 9 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 188 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 206 2 8 94 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 206
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 188 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 206 2 7 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 206 (accept_3_2 13 188 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 206 2 6 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 188 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 206 2 5 94 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 188 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 206 2 4 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 206 (accept_3_2 7 188 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  206 2 3 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 188 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 206 2 2 94 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 206 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 188 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 206 2 1 94 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 206 (accept_3_2 1 188 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 206))))))))))))))))))) (allB_succ' 20 187 206 (Eq.refl
  Bool.true) (allA_of_3_0 20 187 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 186 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 186 206 2 10 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 206 (accept_3_2 19 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 206 2 9 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 206 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 186 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 206 2 8 93 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 206
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 206 2 7 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 206 (accept_3_2 13 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 206 2 6 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 206 2 5 93 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 206
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 206 2 4 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 206 (accept_3_2 7 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  206 2 3 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 186 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 206 2 2 93 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 206 2 1 93 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 206 (accept_3_2 1 186 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 206))))))))))))))))))))) (allB_succ' 22 185 206 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 185 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 20
  185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 185 206 (accept_3_2 19
  185 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 206
  (Polychromatic418967fa.accept_13_5_3_11_1_1288 18 185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 185 206 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 206 (accept_3_2 16 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 185 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 206 (Polychromatic418967fa.accept_10_4_5_6_1_651
  14 185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 206 (accept_3_2 13
  185 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 185 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 206 (accept_3_2 10 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 185 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 206 (Polychromatic418967fa.accept_12_8_5_2_1_746 8
  185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 206 (accept_3_2 7 185
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 6 185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 185 206 (Polychromatic418967fa.accept_13_5_3_11_1_1288 5 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 206 (accept_3_2 4 185 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 185 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  185 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 206 (accept_3_2 1 185
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 206)))))))))))))))))))))) (allB_succ' 23 184 206 (Eq.refl
  Bool.true) (allA_of_3_0 23 184 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 183 206 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 183 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 206 (accept_3_2 22 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 206 (Polychromatic418967fa.accept_9_2_3_8_1_318
  20 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 206 (accept_3_2 19
  183 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 206
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 206 (accept_3_2 16 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 206 (Polychromatic418967fa.accept_9_5_3_8_1_316
  14 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 206 (accept_3_2 13
  183 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 206
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 206 (accept_3_2 10 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 8
  183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 206 (accept_3_2 7 183
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 206
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 206 (accept_3_2 4 183 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 206 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 183 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 206 (accept_3_2 1 183 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  206)))))))))))))))))))))))) (allB_succ' 25 182 206 (Eq.refl Bool.true) (allA_succ_of_gcd 24 182 206 2 12 91 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 23 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 182 206 2 11 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 182 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 182 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 182 206 2 10 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 206 (accept_3_2 19 182 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 206 2 9 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 206 (Polychromatic418967fa.accept_18_17_2_8_1_6800
  17 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 206 2 8 91 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 206
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 206 2 7 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 206 (accept_3_2 13 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 206 2 6 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 206 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 182 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 206 2 5 91 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 206
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 206 2 4 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 206 (accept_3_2 7 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  206 2 3 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 182 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 206 2 2 91 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 182 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 206 2 1 91 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 206 (accept_3_2 1 182 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 206))))))))))))))))))))))))) (allB_succ' 26 181 206 (Eq.refl
  Bool.true) (allA_of_3_0 26 181 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 180 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 180 206 2 13 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 206 (accept_3_2 25 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 206 2 12 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 180 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 206 2 11 90 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 206
  (Polychromatic418967fa.accept_22_21_4_8_1_12043 21 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 180 206 2 10 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 180 206 (accept_3_2 19 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 206 2 9 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 206 (Polychromatic418967fa.accept_16_1_4_14_1_1896 17 180 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 206 2 8 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 180 206 2 7 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 206 (accept_3_2 13 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 206 2 6 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 206 (Polychromatic418967fa.accept_23_11_19_22_1_12042 11 180 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 206 2 5 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 206 2 4 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 206 (accept_3_2 7 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180
  206 2 3 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  180 206 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 180 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 206 2 2 90 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 206 (Polychromatic418967fa.accept_21_3_12_17_1_7471 3 180 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 206 2 1 90 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 206 (accept_3_2 1 180 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 206))))))))))))))))))))))))))) (allB_succ' 28 179 206 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 179 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 206
  (Polychromatic418967fa.accept_19_7_8_16_1_6490 26 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 206 (accept_3_2 25 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 206 (Polychromatic418967fa.accept_17_7_9_2_1_629 24 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 206 (Polychromatic418967fa.accept_10_3_9_6_1_94 23 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 206 (accept_3_2 22 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 206
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 206 (accept_3_2 19 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 206 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 206 (accept_3_2 16 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 206
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 179 206 (accept_3_2 13 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 179 206 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12 179 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 206
  (Polychromatic418967fa.accept_16_11_3_14_1_5043 11 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 179 206 (accept_3_2 10 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 179 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 179 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 206 (accept_3_2 7 179 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 206 (accept_3_2 4 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 206 (Polychromatic418967fa.accept_13_2_10_11_1_1276 2 179 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 206 (accept_3_2 1 179 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 179 206)))))))))))))))))))))))))))) (allB_succ' 29 178 206 (Eq.refl
  Bool.true) (allA_of_3_0 29 178 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 177 206 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 177 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 206 (accept_3_2 28 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 206 (Polychromatic418967fa.accept_7_5_2_3_1_106
  26 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 206 (accept_3_2 25
  177 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 206
  (Polychromatic418967fa.accept_21_3_9_17_1_2983 24 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 206 (accept_3_2 22 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 206 (Polychromatic418967fa.accept_7_6_2_3_1_107
  20 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 206 (accept_3_2 19
  177 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 206
  (Polychromatic418967fa.accept_12_6_9_2_1_311 18 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 206 (accept_3_2 16 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 206 (Polychromatic418967fa.accept_9_5_6_8_1_101
  14 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 206 (accept_3_2 13
  177 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 206
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 206 (accept_3_2 10 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 206 (Polychromatic418967fa.accept_13_9_8_11_1_725 9 177 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 206 (accept_3_2 7 177
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 206
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 206 (accept_3_2 4 177 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 2
  177 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 206 (accept_3_2 1 177
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 206)))))))))))))))))))))))))))))) (allB_succ' 31 176 206
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 176 206 2 15 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 206 2 14 88 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 206
  (Polychromatic418967fa.accept_13_1_7_11_1_702 27 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 206 2 13 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 206 (accept_3_2 25 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 206 2 12 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 176 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 206 2 11 88 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 206 2 10 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 206 (accept_3_2 19 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 206 2 9 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 176 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 206 2 8 88 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 206 2 7 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 206 (accept_3_2 13 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 206 2 6 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 176 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 206 2 5 88 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 206 2 4 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 206 (accept_3_2 7 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  206 2 3 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 176 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 206 2 2 88 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 176 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 206 2 1 88 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 206 (accept_3_2 1 176 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 206))))))))))))))))))))))))))))))) (allB_succ' 32 175 206
  (Eq.refl Bool.true) (allA_of_3_0 32 175 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 174 206 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 174 206 2 16 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 174 206 (accept_3_2 31 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 206 2 15 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 174 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 206 2 14 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 206 2 13 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 206 (accept_3_2 25 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 206 2 12 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 174 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 206 2 11 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 206
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 206 2 10 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 206 (accept_3_2 19 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 206 2 9 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 206 (Polychromatic418967fa.accept_14_3_6_10_1_752 17 174 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 206 2 8 87 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 206
  (Polychromatic418967fa.accept_9_6_3_8_1_595 15 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 206 2 7 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 206 (accept_3_2 13 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 206 2 6 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 206 2 5 87 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 206 2 4 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 206 (accept_3_2 7 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  206 2 3 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 174 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 206 2 2 87 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 206 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 174 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 206 2 1 87 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 206 (accept_3_2 1 174 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 206))))))))))))))))))))))))))))))))) (allB_succ' 34 173 206
  (Eq.refl Bool.true) (allA_succ_of_accept 33 173 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 32 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 206 (accept_3_2 31 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 206 (accept_3_2 28 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 206
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 173 206 (accept_3_2 25 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 173 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 173 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 206 (accept_3_2 22 173 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 21
  173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 206 (accept_3_2 19 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 206 (Polychromatic418967fa.accept_10_7_3_6_1_644 17 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 206 (accept_3_2 16 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 206 (accept_3_2 13 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 206 (accept_3_2 10 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 206 (accept_3_2 7 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 206 (accept_3_2 4 173 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 206 (accept_3_2 1 173 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  206)))))))))))))))))))))))))))))))))) (allB_succ' 35 172 206 (Eq.refl Bool.true) (allA_of_3_0 35 172 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 171 206 (Eq.refl Bool.true) (allA_succ_of_accept 35 171 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 206 (accept_3_2 34 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 32 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 206 (accept_3_2 31 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 171
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 206 (accept_3_2 28 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 206 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 206 (Polychromatic418967fa.accept_27_26_9_17_1_12041 26 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 206 (accept_3_2 25 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 206 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 171
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 206 (accept_3_2 22 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 206 (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 206 (accept_3_2 19 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 171
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 206 (accept_3_2 16 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 206 (Polychromatic418967fa.accept_10_5_1_6_1_672 15 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 171 206 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 206 (accept_3_2 13 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 171
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 206 (accept_3_2 10 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 206 (Polychromatic418967fa.accept_21_8_3_17_1_7399 8 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 206 (accept_3_2 7 171 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 171 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 206 (accept_3_2 4 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 206 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 171 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 171 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 206 (accept_3_2 1 171 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 206)))))))))))))))))))))))))))))))))))) (allB_succ' 37 170 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 170 206 2 18 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 206 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 170 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 206 2 17 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 206
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 206 2 16 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 206 (accept_3_2 31 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 206 2 15 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 170 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 206 2 14 85 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 206
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 206 2 13 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 206 (accept_3_2 25 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 206 2 12 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 206 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 170 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 206 2 11 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 206
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 206 2 10 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 206 (accept_3_2 19 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 206 2 9 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 206 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 170 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 206 2 8 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 206
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 206 2 7 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 206 (accept_3_2 13 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 206 2 6 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 206 (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 170 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 206 2 5 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 206
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 206 2 4 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 206 (accept_3_2 7 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  206 2 3 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 170 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 206 2 2 85 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 206 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 170 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 206 2 1 85 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 206 (accept_3_2 1 170 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 206))))))))))))))))))))))))))))))))))))) (allB_succ' 38 169 206
  (Eq.refl Bool.true) (allA_of_3_0 38 169 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 168 206 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 168 206 2 19 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 168 206 (accept_3_2 37 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 206 2 18 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 206 (Polychromatic418967fa.accept_25_10_18_6_1_12040 35 168 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 206 2 17 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 206
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 168 206 2 16 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 168 206 (accept_3_2 31 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 206 2 15 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 206 2 14 84 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 206
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 206 2 13 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 206 (accept_3_2 25 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 206 2 12 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 206 2 11 84 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 206 2 10 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 206 (accept_3_2 19 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 206 2 9 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 206 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 168 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 206 2 8 84 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 206
  (Polychromatic418967fa.accept_23_15_7_22_1_12021 15 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 206 2 7 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 206 (accept_3_2 13 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 206 2 6 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 206 2 5 84 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 206
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 9 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 206 2 4 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 206 (accept_3_2 7 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  206 2 3 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 206 2 2 84 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 206 2 1 84 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 206 (accept_3_2 1 168 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 206))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 167
  206 (Eq.refl Bool.true) (allA_succ_of_accept 39 167 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 206 (accept_3_2 37 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 206 (Polychromatic418967fa.accept_15_6_2_11_1_325 36 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 206 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 206 (accept_3_2 34 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 206
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 206 (accept_3_2 31 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 206 (accept_3_2 28 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 206
  (Polychromatic418967fa.accept_16_10_7_14_1_2882 26 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 167 206 (accept_3_2 25 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 167 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 206 (accept_3_2 22 167 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 206 (accept_3_2 19 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 206 (accept_3_2 16 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 206
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 206 (accept_3_2 13 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 206 (accept_3_2 10 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 206 (accept_3_2 7 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 206 (accept_3_2 4 167 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 206 (accept_3_2 1 167 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  206)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 166 206 (Eq.refl Bool.true) (allA_of_3_0 41 166 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 165 206 (Eq.refl Bool.true) (allA_succ_of_accept 41 165 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 206 (accept_3_2 40 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 206 (accept_3_2 37 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 206 (accept_3_2 34 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 206 (accept_3_2 31 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 206 (accept_3_2 28 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 206 (Polychromatic418967fa.accept_16_10_5_14_1_6173 26 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 206 (accept_3_2 25 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 206 (accept_3_2 22 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 206 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 206 (accept_3_2 19 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 206 (accept_3_2 16 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 206 (accept_3_2 13 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 206 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 165 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 206 (accept_3_2 10 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 206 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 206 (accept_3_2 7 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 165 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 206 (accept_3_2 4 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 206 (accept_3_2 1 165 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 206)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 164 206 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 164 206 2 21 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 164 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 164 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 206 2 20 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 206
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 206 2 19 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 206 (accept_3_2 37 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 206 2 18 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 206 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 164 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 206 2 17 82 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 206
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 206 2 16 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 206 (accept_3_2 31 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 206 2 15 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 164 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 206 2 14 82 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 206
  (Polychromatic418967fa.accept_13_1_8_11_1_724 27 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 206 2 13 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 206 (accept_3_2 25 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 206 2 12 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 164 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 206 2 11 82 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 206
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 206 2 10 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 206 (accept_3_2 19 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 206 2 9 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 164 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 206 2 8 82 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 206
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 206 2 7 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 206 (accept_3_2 13 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 206 2 6 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 164 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 206 2 5 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 206
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 206 2 4 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 206 (accept_3_2 7 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  206 2 3 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 206 2 2 82 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 164 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 206 2 1 82 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 206 (accept_3_2 1 164 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 206))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  163 206 (Eq.refl Bool.true) (allA_of_3_0 44 163 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 162 206
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 162 206 2 22 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 206 (accept_3_2 43 162 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 162 206 2 21 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 162 206 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 162 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 206 2 20 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 206
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 206 2 19 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 206 (accept_3_2 37 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 206 2 18 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 206 (Polychromatic418967fa.accept_21_14_15_17_1_2972 35 162 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 206 2 17 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 206
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 206 2 16 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 206 (accept_3_2 31 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 206 2 15 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 206 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 162 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 206 2 14 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 206 2 13 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 206 (accept_3_2 25 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 206 2 12 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 206 2 11 81 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 206
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 206 2 10 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 206 (accept_3_2 19 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 206 2 9 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 206 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 162 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 206 2 8 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 206 2 7 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 206 (accept_3_2 13 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 206 2 6 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 162 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 206 2 5 81 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 206 2 4 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 206 (accept_3_2 7 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  206 2 3 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 162 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 206 2 2 81 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 206 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 162 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 206 2 1 81 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 206 (accept_3_2 1 162 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 206))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  161 206 (Eq.refl Bool.true) (allA_succ_of_accept 45 161 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 206 (accept_3_2 43 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 206 (Polychromatic418967fa.accept_18_5_17_8_1_2984 41 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 206 (accept_3_2 40 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 206
  (Polychromatic418967fa.accept_18_2_17_8_1_1893 38 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 206 (accept_3_2 37 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 206 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 206 (accept_3_2 34 161 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 206
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 206 (accept_3_2 31 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 206 (Polychromatic418967fa.accept_21_9_14_17_1_12039 30 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 206 (Polychromatic418967fa.accept_13_3_5_11_1_716 29 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 206 (accept_3_2 28 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 206
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 206 (accept_3_2 25 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 206 (Polychromatic418967fa.accept_21_3_14_17_1_10628 24 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 206 (accept_3_2 22 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 206 (accept_3_2 19 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 206 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 206 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 206 (accept_3_2 16 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 206
  (Polychromatic418967fa.accept_19_14_9_16_1_7969 14 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 161 206 (accept_3_2 13 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 161 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 161 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 206 (accept_3_2 10 161 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 206 (accept_3_2 7 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 206 (Polychromatic418967fa.accept_13_6_5_11_1_1971 6 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 206 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 161 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 206 (accept_3_2 4 161 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 206
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 206 (accept_3_2 1 161 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  206)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 160 206 (Eq.refl Bool.true) (allA_of_3_0 47 160 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 159 206 (Eq.refl Bool.true) (allA_succ_of_accept 47 159 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 206 (accept_3_2 46 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 206 (accept_3_2 43 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 206 (accept_3_2 40 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 206 (accept_3_2 37 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 206 (accept_3_2 34 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 206 (accept_3_2 31 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 206 (accept_3_2 28 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 206 (Polychromatic418967fa.accept_13_1_3_11_1_1289 27 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 206 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 206 (accept_3_2 25 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 206 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 159
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 206 (accept_3_2 22 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 206 (accept_3_2 19 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 206 (accept_3_2 16 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 206 (accept_3_2 13 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 206 (accept_3_2 10 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 206 (accept_3_2 7 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 159 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 206 (accept_3_2 4 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 206 (accept_3_2 1 159 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 206)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 158 206 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 158 206 2 24 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 158 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 158 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 206 2 23 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 206
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 206 2 22 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 206 (accept_3_2 43 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 206 2 21 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 158 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 206 2 20 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 206 2 19 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 206 (accept_3_2 37 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 206 2 18 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 206 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 158 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 206 2 17 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 206 2 16 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 206 (accept_3_2 31 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 206 2 15 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 158 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 206 2 14 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 206
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 206 2 13 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 206 (accept_3_2 25 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 206 2 12 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 206 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 158 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 206 2 11 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 206 2 10 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 206 (accept_3_2 19 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 206 2 9 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 206 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 158 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 206 2 8 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 206
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 206 2 7 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 206 (accept_3_2 13 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 206 2 6 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 206 2 5 79 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 206
  (Polychromatic418967fa.accept_13_9_2_11_1_1964 9 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 206 2 4 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 206 (accept_3_2 7 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  206 2 3 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 206 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 158 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 206 2 2 79 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 158 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 206 2 1 79 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 206 (accept_3_2 1 158 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 206)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 157 206 (Eq.refl Bool.true) (allA_of_3_0 50 157 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 156 206 (Eq.refl Bool.true) (allA_succ_of_gcd 50 156 206 2 25 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 206 (accept_3_2 49 156 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 156 206 2 24 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 156 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 47
  156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 206 2 23 78 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 206
  (Polychromatic418967fa.accept_17_11_3_2_1_5867 45 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 206 2 22 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 206 (accept_3_2 43 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 206 2 21 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 156 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 206 2 20 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 206
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 39 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 206 2 19 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 206 (accept_3_2 37 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 206 2 18 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 206 (Polychromatic418967fa.accept_15_5_6_11_1_854 35 156 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 206 2 17 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 206
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 206 2 16 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 206 (accept_3_2 31 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 206 2 15 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 206 2 14 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 206
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 206 2 13 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 206 (accept_3_2 25 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 206 2 12 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 206 2 11 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 206
  (Polychromatic418967fa.accept_18_3_12_8_1_5415 21 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 206 2 10 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 156 206 (accept_3_2 19 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 206 2 9 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 206 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 156 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 206 2 8 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 206
  (Polychromatic418967fa.accept_7_1_2_3_1_257 15 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 206 2 7 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 206 (accept_3_2 13 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 206 2 6 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 156 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 206 2 5 78 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 206
  (Polychromatic418967fa.accept_15_9_6_11_1_1586 9 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 206 2 4 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 206 (accept_3_2 7 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  206 2 3 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 206 2 2 78 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 206 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 156 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 206 2 1 78 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 206 (accept_3_2 1 156 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156 206)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 155 206 (Eq.refl Bool.true) (allA_succ_of_accept 51 155 206 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 206 (accept_3_2 49 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 206 (accept_3_2 46 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 206 (accept_3_2 43 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 206 (accept_3_2 40 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 206
  (Polychromatic418967fa.accept_15_8_5_11_1_2358 38 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 206 (accept_3_2 37 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 206 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 206 (Polychromatic418967fa.accept_16_3_11_14_1_446 35 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 206 (accept_3_2 34 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 206
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 206 (accept_3_2 31 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 155 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 206 (accept_3_2 28 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 206
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 206 (accept_3_2 25 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 206 (accept_3_2 22 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 206 (accept_3_2 19 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 206 (accept_3_2 16 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 206 (accept_3_2 13 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 206 (accept_3_2 10 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 206 (accept_3_2 7 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 206 (accept_3_2 4 155 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 206 (accept_3_2 1 155 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  206)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 154 206 (Eq.refl Bool.true) (allA_of_3_0 53 154
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 153 206 (Eq.refl Bool.true) (allA_succ_of_accept 53 153
  206 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 206 (accept_3_2 52 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 153 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 153 206 (Polychromatic418967fa.accept_27_23_18_17_1_12038 50 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 206 (accept_3_2 49 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 153
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 206 (accept_3_2 46 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 206 (Polychromatic418967fa.accept_14_3_13_10_1_761 45 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 206 (accept_3_2 43 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 206 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 206 (accept_3_2 40 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 206 (accept_3_2 37 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 206 (Polychromatic418967fa.accept_15_6_3_11_1_848 36 153
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 206 (accept_3_2 34 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 206 (Polychromatic418967fa.accept_21_12_6_17_1_12037 33 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 206 (accept_3_2 31 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 153 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 206 (accept_3_2 28 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 206 (Polychromatic418967fa.accept_22_4_21_8_1_8923 26 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 206 (accept_3_2 25 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 206 (Polychromatic418967fa.accept_18_6_9_8_1_6812 24 153
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 206 (accept_3_2 22 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 206 (Polychromatic418967fa.accept_13_8_10_11_1_2730 21 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 206 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 206 (accept_3_2 19 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 153 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 206 (accept_3_2 16 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 206 (Polychromatic418967fa.accept_13_1_10_11_1_1280 14 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 206 (accept_3_2 13 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 206 (Polychromatic418967fa.accept_13_12_10_11_1_1279 12
  153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 206 (accept_3_2 10 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 206 (accept_3_2 7 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 153 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 206 (accept_3_2 4 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 206 (accept_3_2 1 153 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 206)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 152 206
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 152 206 2 27 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 152 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 152 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 206 2 26 76 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 206 2 25 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 206 (accept_3_2 49 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 206 2 24 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 152 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 206 2 23 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 206
  (Polychromatic418967fa.accept_20_5_12_6_1_7806 45 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 206 2 22 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 206 (accept_3_2 43 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 206 2 21 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 206 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 152 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 206 2 20 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 206
  (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 206 2 19 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 206 (accept_3_2 37 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 206 2 18 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 152 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 206 2 17 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 206
  (Polychromatic418967fa.accept_13_7_9_11_1_705 33 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 206 2 16 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 206 (accept_3_2 31 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 206 2 15 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 152 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 206 2 14 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 206
  (Polychromatic418967fa.accept_13_1_9_11_1_703 27 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 206 2 13 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 206 (accept_3_2 25 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 206 2 12 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 206 2 11 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 206
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 206 2 10 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 206 (accept_3_2 19 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 206 2 9 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 152 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 206 2 8 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 206 2 7 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 206 (accept_3_2 13 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 206 2 6 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 206 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 152 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 206 2 5 76 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 206 2 4 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 206 (accept_3_2 7 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  206 2 3 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 152 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 206 2 2 76 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 206 (Polychromatic418967fa.accept_22_3_20_8_1_8985 3 152 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 206 2 1 76 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 206 (accept_3_2 1 152 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 206)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 151 206 (Eq.refl Bool.true) (allA_of_3_0 56 151 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 150 206 (Eq.refl Bool.true) (allA_succ_of_gcd 56 150 206 2 28 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 206 (accept_3_2 55 150 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 150 206 2 27 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 150 206 (Polychromatic418967fa.accept_13_1_7_11_1_702
  53 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 206 2 26 75 103
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 51 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 206 2 25 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 206 (accept_3_2 49 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 206 2 24 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 150 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 206 2 23 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 206
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 206 2 22 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 206 (accept_3_2 43 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 206 2 21 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 150 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 206 2 20 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 206 2 19 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 206 (accept_3_2 37 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 206 2 18 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 206 (Polychromatic418967fa.accept_13_9_7_11_1_1292 35 150 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 206 2 17 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 206
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 206 2 16 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 206 (accept_3_2 31 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 206 2 15 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 150 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 206 2 14 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 206 2 13 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 206 (accept_3_2 25 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 206 2 12 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 150 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 206 2 11 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 206 2 10 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 206 (accept_3_2 19 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 206 2 9 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 206 (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 150 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 206 2 8 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 206
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 206 2 7 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 206 (accept_3_2 13 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 206 2 6 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 206 2 5 75 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 206
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 206 2 4 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 206 (accept_3_2 7 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  206 2 3 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 150 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 206 2 2 75 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 206 2 1 75 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 206 (accept_3_2 1 150 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 149 206 (Eq.refl Bool.true) (allA_succ_of_accept 57 149 206 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 149 206 (accept_3_2 55 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 149 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 149 206 (Polychromatic418967fa.accept_10_3_9_6_1_94 53 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 206 (accept_3_2 52 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 206
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 206 (accept_3_2 49 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 206 (accept_3_2 46 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 206 (accept_3_2 43 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 206 (accept_3_2 40 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 206 (accept_3_2 37 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 206 (accept_3_2 34 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 206
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 206 (accept_3_2 31 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 206 (accept_3_2 28 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 206
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 206 (accept_3_2 25 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 206 (accept_3_2 22 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 206
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 206 (accept_3_2 19 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 206 (Polychromatic418967fa.accept_13_5_6_11_1_1933 18 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 206 (Polychromatic418967fa.accept_13_4_6_11_1_2017 17 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 206 (accept_3_2 16 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 206
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 206 (accept_3_2 13 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 206 (accept_3_2 10 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 206
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 206 (accept_3_2 7 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 206 (accept_3_2 4 149 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 206 (accept_3_2 1 149 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 148 206 (Eq.refl Bool.true) (allA_of_3_0
  59 148 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 147 206 (Eq.refl Bool.true) (allA_succ_of_accept 59
  147 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 147 206 (accept_3_2 58 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 147 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 206 (accept_3_2 55 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 206 (Polychromatic418967fa.accept_12_6_3_2_1_743
  54 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 206 (accept_3_2 52 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 206 (accept_3_2 49 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 206 (Polychromatic418967fa.accept_18_12_3_8_1_6817 48 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 206 (accept_3_2 46 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 206 (Polychromatic418967fa.accept_15_14_12_11_1_1572 44 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 206 (accept_3_2 43 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 206 (accept_3_2 40 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 206 (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 206 (accept_3_2 37 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 206 (Polychromatic418967fa.accept_13_10_4_11_1_1969 36 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 206 (accept_3_2 34 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 206 (accept_3_2 31 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 206 (accept_3_2 28 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 206 (Polychromatic418967fa.accept_16_11_3_14_1_5043 27 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 206 (Polychromatic418967fa.accept_17_9_11_2_1_5894 26 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 206 (accept_3_2 25 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 206 (accept_3_2 22 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 206 (accept_3_2 19 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 206 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 206 (accept_3_2 16 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 206 (accept_3_2 13 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 206 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 206 (accept_3_2 10 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 206 (Polychromatic418967fa.accept_13_8_4_11_1_3469 8 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 206 (accept_3_2 7 147 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 206 (accept_3_2 4 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 206 (Polychromatic418967fa.accept_10_3_7_6_1_659 3 147 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 206 (accept_3_2 1 147 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 146
  206 (Eq.refl Bool.true) (allA_succ_of_gcd 60 146 206 2 30 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 146 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 146 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 206 2 29 73 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 206
  (Polychromatic418967fa.accept_9_3_2_8_1_108 57 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 146 206 2 28 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 146 206 (accept_3_2 55 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 206 2 27 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 146 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 206 2 26 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 206 2 25 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 206 (accept_3_2 49 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 206 2 24 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 206 (Polychromatic418967fa.accept_13_8_3_11_1_3467 47 146 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 206 2 23 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 206
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 206 2 22 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 206 (accept_3_2 43 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 206 2 21 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 206 2 20 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 206
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 206 2 19 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 206 (accept_3_2 37 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 206 2 18 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 206 (Polychromatic418967fa.accept_18_17_2_8_1_6800 35 146 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 206 2 17 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 206
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 206 2 16 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 206 (accept_3_2 31 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 206 2 15 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 206 (Polychromatic418967fa.accept_17_12_10_2_1_5835 29 146 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 206 2 14 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 206
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 206 2 13 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 206 (accept_3_2 25 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 206 2 12 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 146 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 206 2 11 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 206
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 206 2 10 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 206 (accept_3_2 19 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 206 2 9 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 206 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 146 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 206 2 8 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 206
  (Polychromatic418967fa.accept_9_6_2_8_1_592 15 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 206 2 7 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 206 (accept_3_2 13 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 206 2 6 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 146 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 206 2 5 73 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 206 2 4 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 206 (accept_3_2 7 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  206 2 3 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 206 2 2 73 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 146 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 206 2 1 73 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 206 (accept_3_2 1 146 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 145 206 (Eq.refl Bool.true)
  (allA_of_3_0 62 145 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 144 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 144 206 2 31 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 206 (accept_3_2 61 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 206 2 30 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 206 (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 206 2 29 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 206
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 206 2 28 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 206 (accept_3_2 55 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 206 2 27 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 206 (Polychromatic418967fa.accept_19_15_11_16_1_6492 53 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 206 2 26 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 206
  (Polychromatic418967fa.accept_13_12_1_11_1_1917 51 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 144 206 2 25 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 144 206 (accept_3_2 49 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 206 2 24 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 206 (Polychromatic418967fa.accept_13_8_1_11_1_1284 47 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 206 2 23 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 206
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 206 2 22 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 206 (accept_3_2 43 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 206 2 21 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 206 2 20 72 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 206
  (Polychromatic418967fa.accept_23_16_6_22_1_12036 39 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 144 206 2 19 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 144 206 (accept_3_2 37 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 206 2 18 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 206 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 144 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 206 2 17 72 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 206
  (Polychromatic418967fa.accept_13_7_1_11_1_732 33 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 206 2 16 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 206 (accept_3_2 31 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 206 2 15 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 206 2 14 72 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 206
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 206 2 13 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 206 (accept_3_2 25 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 206 2 12 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 206 (Polychromatic418967fa.accept_13_10_1_11_1_1961 23 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 206 2 11 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 206
  (Polychromatic418967fa.accept_13_8_1_11_1_1284 21 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 206 2 10 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 206 (accept_3_2 19 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 206 2 9 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 206 (Polychromatic418967fa.accept_15_2_9_11_1_1551 17 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 206 2 8 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 206
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 144 206 2 7 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 144 206 (accept_3_2 13 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 206 2 6 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 206 (Polychromatic418967fa.accept_17_11_8_2_1_3398 11 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 206 2 5 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 206
  (Polychromatic418967fa.accept_13_9_1_11_1_275 9 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 206 2 4 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 206 (accept_3_2 7 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  206 2 3 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 206 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 144 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 206 2 2 72 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 206 (Polychromatic418967fa.accept_13_3_1_11_1_1268 3 144 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 206 2 1 72 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 206 (accept_3_2 1 144 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 143 206 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 206 (Polychromatic418967fa.accept_14_6_3_10_1_3905 62 143
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 206 (accept_3_2 61 143
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 206
  (Polychromatic418967fa.accept_17_9_7_2_1_2347 60 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 143 206 (Polychromatic418967fa.accept_10_9_3_6_1_686 59 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 206 (accept_3_2 58 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 206 (accept_3_2 55 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 206 (Polychromatic418967fa.accept_22_10_11_8_1_5624 54 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 206 (accept_3_2 52 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 206
  (Polychromatic418967fa.accept_15_5_8_11_1_2350 50 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 206 (accept_3_2 49 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 206 (Polychromatic418967fa.accept_10_7_3_6_1_644 47 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 206 (accept_3_2 46 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 206 (accept_3_2 43 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 206 (Polychromatic418967fa.accept_15_12_8_11_1_4383 42 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 206 (accept_3_2 40 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 206
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 206 (accept_3_2 37 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 206 (Polychromatic418967fa.accept_16_4_15_14_1_5056 36 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 206 (Polychromatic418967fa.accept_14_7_3_10_1_1364 35 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 206 (accept_3_2 34 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 143 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 206 (accept_3_2 31 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 206 (Polychromatic418967fa.accept_17_13_7_2_1_4562 30 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 206 (accept_3_2 28 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 206
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 26 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 143 206 (accept_3_2 25 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 206 (Polychromatic418967fa.accept_19_5_10_16_1_6507 24 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 206
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 143 206 (accept_3_2 22 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 206 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 143
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 206 (accept_3_2 19 143
  206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 206
  (Polychromatic418967fa.accept_10_8_3_6_1_685 18 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 206 (accept_3_2 16 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 206
  (Polychromatic418967fa.accept_22_14_11_8_1_7212 14 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 143 206 (accept_3_2 13 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 143 206 (Polychromatic418967fa.accept_15_12_8_11_1_4383 12 143 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 206
  (Polychromatic418967fa.accept_24_11_23_14_1_12035 11 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 143 206 (accept_3_2 10 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 143 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 206 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 143 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 206 (accept_3_2 7 143 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 206 (Polychromatic418967fa.accept_14_6_3_10_1_3905
  6 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 206 (accept_3_2 4 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 206 (Polychromatic418967fa.accept_18_2_17_8_1_1893 2 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 206 (accept_3_2 1 143 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 143 206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 142 206 (Eq.refl Bool.true) (allA_of_3_0 65 142 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 66 141 206 (Eq.refl Bool.true) (allA_succ_of_accept 65 141 206 (Polychromatic418967fa.accept_6_5_3_2_1_68
  65 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 206 (accept_3_2 64
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 141 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 62 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 206 (accept_3_2 61 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 141 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 59
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 206 (accept_3_2 58
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 206 (accept_3_2 55 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 53
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 206 (accept_3_2 52
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 50 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 206 (accept_3_2 49 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 206 (accept_3_2 46
  141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 206
  (Polychromatic418967fa.accept_10_5_1_6_1_672 45 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 206 (accept_3_2 43 141 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 206 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 206 (accept_3_2 40 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 206 (accept_3_2 37 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 206 (Polychromatic418967fa.accept_19_17_8_16_1_12029 36 141 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 206 (accept_3_2 34 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 206 (accept_3_2 31 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 206 (accept_3_2 28 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 206 (accept_3_2 25 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 206 (Polychromatic418967fa.accept_15_9_6_11_1_1586 24 141 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 206 (accept_3_2 22 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 206 (accept_3_2 19 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 206 (accept_3_2 16 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 206 (accept_3_2 13 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 206 (accept_3_2 10 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 206 (Polychromatic418967fa.accept_21_8_15_17_1_4382 8 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 206 (accept_3_2 7 141 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 141 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 206 (accept_3_2 4 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 206 (accept_3_2 1 141 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 140 206 (Eq.refl Bool.true) (allA_succ_of_gcd 66 140 206 2 33 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 140 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 65
  140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 206 2 32 70 103 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 206
  (Polychromatic418967fa.accept_17_12_4_2_1_7116 63 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 206 2 31 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 206 (accept_3_2 61 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 206 2 30 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 140 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 206 2 29 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 57 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 206 2 28 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 206 (accept_3_2 55 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 206 2 27 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 206 2 26 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 51 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 206 2 25 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 206 (accept_3_2 49 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 206 2 24 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 206 2 23 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 206
  (Polychromatic418967fa.accept_21_3_14_17_1_10628 45 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 206 2 22 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 206 (accept_3_2 43 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 206 2 21 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 206 2 20 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 206 2 19 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 206 (accept_3_2 37 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 206 2 18 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 140 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 206 2 17 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 33 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 206 2 16 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 206 (accept_3_2 31 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 206 2 15 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 206 2 14 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 206
  (Polychromatic418967fa.accept_13_1_10_11_1_1280 27 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 140 206 2 13 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 140 206 (accept_3_2 25 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 206 2 12 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 206 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 206 2 11 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 206
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 206 2 10 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 206 (accept_3_2 19 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 206 2 9 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 206 2 8 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 206
  (Polychromatic418967fa.accept_9_6_5_8_1_598 15 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 206 2 7 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 206 (accept_3_2 13 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 206 2 6 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 140 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 206 2 5 70 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 206
  (Polychromatic418967fa.accept_15_9_5_11_1_5416 9 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 206 2 4 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 206 (accept_3_2 7 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  206 2 3 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 206 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 206 2 2 70 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 140 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 140 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 206 2 1 70 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 206 (accept_3_2 1 140 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 139 206 (Eq.refl Bool.true)
  (allA_of_3_0 68 139 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 138 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 138 206 2 34 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 206 (accept_3_2 67 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 206 2 33 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 206 2 32 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 206
  (Polychromatic418967fa.accept_10_3_8_6_1_326 63 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 206 2 31 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 206 (accept_3_2 61 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 206 2 30 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 206 2 29 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 206 2 28 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 206 (accept_3_2 55 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 206 2 27 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 206 (Polychromatic418967fa.accept_10_3_8_6_1_326 53 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 206 2 26 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 206 2 25 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 206 (accept_3_2 49 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 206 2 24 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 206 2 23 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 206
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 206 2 22 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 206 (accept_3_2 43 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 206 2 21 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 206 2 20 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 206 2 19 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 206 (accept_3_2 37 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 206 2 18 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 206 (Polychromatic418967fa.accept_13_9_8_11_1_725 35 138 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 206 2 17 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 206
  (Polychromatic418967fa.accept_9_6_3_8_1_595 33 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 206 2 16 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 206 (accept_3_2 31 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 206 2 15 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 206 2 14 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 206
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 206 2 13 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 206 (accept_3_2 25 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 206 2 12 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 206 2 11 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 206
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 206 2 10 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 206 (accept_3_2 19 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 206 2 9 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 206 (Polychromatic418967fa.accept_13_4_8_11_1_1937 17 138 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 206 2 8 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 206 2 7 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 206 (accept_3_2 13 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 206 2 6 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 206 2 5 69 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 206 2 4 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 206 (accept_3_2 7 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  206 2 3 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 138 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 206 2 2 69 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 206 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 206 2 1 69 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 206 (accept_3_2 1 138 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 137 206 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 206 (accept_3_2 67 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 206 (Polychromatic418967fa.accept_9_3_2_8_1_108
  66 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 206
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 137 206 (accept_3_2 64 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 137 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 62 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 206 (accept_3_2 61 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 137 206 (accept_3_2 58 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 206 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 206 (accept_3_2 55 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 206 (Polychromatic418967fa.accept_15_9_2_11_1_2391 54 137
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 206
  (Polychromatic418967fa.accept_10_3_7_6_1_659 53 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 206 (accept_3_2 52 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 206 (accept_3_2 49 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 206 (accept_3_2 46 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 206 (Polychromatic418967fa.accept_12_8_5_2_1_746 44 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 206 (accept_3_2 43 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 206
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 206 (accept_3_2 40 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 206 (Polychromatic418967fa.accept_13_12_7_11_1_1935 38 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 206 (accept_3_2 37 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 206 (accept_3_2 34 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 206 (accept_3_2 31 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 206
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 206 (accept_3_2 28 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 206 (Polychromatic418967fa.accept_19_7_4_16_1_9325 26 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 206 (accept_3_2 25 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 206 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 206 (accept_3_2 22 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 206 (accept_3_2 19 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 206 (Polychromatic418967fa.accept_13_5_7_11_1_3470 18 137 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 206
  (Polychromatic418967fa.accept_13_4_7_11_1_1981 17 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 206 (accept_3_2 16 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 206 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 206 (accept_3_2 13 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 206 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 206 (accept_3_2 10 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 206 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 206 (accept_3_2 7 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 206 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 137 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 206
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 206 (accept_3_2 4 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 206 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 206 (accept_3_2 1 137 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 71 136 206 (Eq.refl Bool.true) (allA_of_3_0 71 136 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 72 135 206 (Eq.refl Bool.true) (allA_succ_of_accept 71 135 206 (Polychromatic418967fa.accept_6_5_3_2_1_68
  71 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 206 (accept_3_2 70
  135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 68 135 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 206 (accept_3_2 67 135 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 65 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 206 (accept_3_2 64 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 206 (Polychromatic418967fa.accept_16_15_7_14_1_2883 63 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 206 (accept_3_2 61 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 206 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 206 (accept_3_2 58 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 206 (Polychromatic418967fa.accept_17_5_16_2_1_7094 56 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 206 (accept_3_2 55 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 135 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 206 (accept_3_2 52 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 206 (Polychromatic418967fa.accept_10_1_5_6_1_649 51 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 206 (accept_3_2 49 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 206 (accept_3_2 46 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 206 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 206 (accept_3_2 43 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 135
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 206 (accept_3_2 40 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 206 (Polychromatic418967fa.accept_10_9_5_6_1_691 39 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 206 (Polychromatic418967fa.accept_11_5_3_8_1_454 38 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 206 (accept_3_2 37 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 135 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 206 (accept_3_2 34 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 206 (Polychromatic418967fa.accept_13_6_5_11_1_1971 32 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 206 (accept_3_2 31 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 135
  206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 206 (accept_3_2 28 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 206 (accept_3_2 25 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 206 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 206 (accept_3_2 22 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 206 (accept_3_2 19 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 206 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 206 (accept_3_2 16 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 206 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 206 (accept_3_2 13 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 206 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 206 (accept_3_2 10 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 206 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 206 (accept_3_2 7 135 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 206 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 206
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 206 (accept_3_2 4 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 206 (Polychromatic418967fa.accept_13_3_5_11_1_716 3 135 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 206 (Polychromatic418967fa.accept_21_2_9_17_1_4376 2 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 206 (accept_3_2 1 135 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135
  206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 134 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 134 206 2 36 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 206 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 206 2 35 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 206
  (Polychromatic418967fa.accept_20_9_14_6_1_320 69 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 206 2 34 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 206 (accept_3_2 67 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 206 2 33 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 206 2 32 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 206
  (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 134 206 2 31 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 134 206 (accept_3_2 61 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 206 2 30 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 206 (Polychromatic418967fa.accept_13_7_4_11_1_1967 59 134 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 206 2 29 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 206
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 57 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 134 206 2 28 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 134 206 (accept_3_2 55 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 206 2 27 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 206 2 26 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 206 2 25 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 206 (accept_3_2 49 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 206 2 24 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 206 2 23 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 206
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 206 2 22 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 206 (accept_3_2 43 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 206 2 21 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 206 (Polychromatic418967fa.accept_13_2_4_11_1_2003 41 134 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 206 2 20 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 206
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 206 2 19 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 206 (accept_3_2 37 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 206 2 18 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 206 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 206 2 17 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 206
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 206 2 16 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 206 (accept_3_2 31 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 206 2 15 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 206 (Polychromatic418967fa.accept_19_10_1_16_1_7977 29 134 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 206 2 14 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 206
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 206 2 13 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 206 (accept_3_2 25 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 206 2 12 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 206 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 206 2 11 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 206
  (Polychromatic418967fa.accept_13_8_4_11_1_3469 21 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 206 2 10 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 206 (accept_3_2 19 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 206 2 9 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 206 (Polychromatic418967fa.accept_19_17_1_16_1_1443 17 134 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 206 2 8 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 206
  (Polychromatic418967fa.accept_10_5_4_6_1_319 15 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 206 2 7 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 206 (accept_3_2 13 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 206 2 6 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 206 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 134 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 206 2 5 67 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 206
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 206 2 4 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 206 (accept_3_2 7 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  206 2 3 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 206 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 134 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 206 2 2 67 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 206 (Polychromatic418967fa.accept_15_3_14_11_1_1579 3 134 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 206 2 1 67 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 206 (accept_3_2 1 134 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 133 206 (Eq.refl
  Bool.true) (allA_of_3_0 74 133 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 132 206 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 132 206 2 37 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 206 (accept_3_2 73 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 206 2 36 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 206 (Polychromatic418967fa.accept_10_1_2_6_1_638 71 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 206 2 35 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 206
  (Polychromatic418967fa.accept_13_4_2_11_1_733 69 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 206 2 34 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 206 (accept_3_2 67 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 206 2 33 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 206 2 32 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 206
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 63 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 206 2 31 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 206 (accept_3_2 61 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 206 2 30 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 59 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 206 2 29 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 57 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 206 2 28 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 206 (accept_3_2 55 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 206 2 27 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 206 2 26 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 206 2 25 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 206 (accept_3_2 49 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 206 2 24 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 206 2 23 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 206
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 206 2 22 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 206 (accept_3_2 43 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 206 2 21 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 206 2 20 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 206
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 206 2 19 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 206 (accept_3_2 37 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 206 2 18 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 206 (Polychromatic418967fa.accept_13_9_2_11_1_1964 35 132 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 206 2 17 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 206
  (Polychromatic418967fa.accept_16_1_4_14_1_1896 33 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 132 206 2 16 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 132 206 (accept_3_2 31 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 206 2 15 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 206 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 206 2 14 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 206
  (Polychromatic418967fa.accept_18_9_6_8_1_2989 27 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 206 2 13 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 206 (accept_3_2 25 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 206 2 12 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 206 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 206 2 11 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 206
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 206 2 10 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 206 (accept_3_2 19 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 206 2 9 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 206 (Polychromatic418967fa.accept_13_4_2_11_1_733 17 132 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 206 2 8 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 206
  (Polychromatic418967fa.accept_16_15_4_14_1_6123 15 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 206 2 7 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 206 (accept_3_2 13 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 206 2 6 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 206 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 206 2 5 66 103 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 206
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 206 2 4 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 206 (accept_3_2 7 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  206 2 3 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 206 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 206 2 2 66 103 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 206 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 132 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 206 2 1 66 103 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 206 (accept_3_2 1 132 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 131 206 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 74
  131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 206 (accept_3_2 73
  131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 131 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 131 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 206 (accept_3_2 70 131 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 206
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 206 (accept_3_2 67 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 206 (accept_3_2 64 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 206
  (Polychromatic418967fa.accept_10_2_1_6_1_634 62 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 206 (accept_3_2 61 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 60 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 206 (Polychromatic418967fa.accept_13_7_1_11_1_732 59 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 206 (accept_3_2 58 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 206 (accept_3_2 55 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 206 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 206 (accept_3_2 52 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 206 (accept_3_2 49 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 206 (accept_3_2 46 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 206 (accept_3_2 43 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 206 (accept_3_2 40 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 206 (accept_3_2 37 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 206 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 206 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 206 (accept_3_2 34 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 206
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 206 (accept_3_2 31 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 206 (accept_3_2 28 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 206
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 131 206 (accept_3_2 25 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 131 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 206 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 206 (accept_3_2 22 131 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 206
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 206 (accept_3_2 19 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 206 (Polychromatic418967fa.accept_19_18_17_16_1_6494 18 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 206 (accept_3_2 16 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 206
  (Polychromatic418967fa.accept_18_14_5_8_1_1880 14 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 206 (accept_3_2 13 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 206 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 206 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 206 (accept_3_2 10 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 206
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 206 (accept_3_2 7 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 206 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 206 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 206 (accept_3_2 4 131 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 206 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 206
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 206 (accept_3_2 1 131 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  206)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 130 206 (Eq.refl
  Bool.true) (allA_of_3_0 77 130 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 129 206 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 129 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 206 (accept_3_2 76 129 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 206 (Polychromatic418967fa.accept_9_2_3_8_1_318
  74 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 206 (accept_3_2 73
  129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 206
  (Polychromatic418967fa.accept_13_7_12_11_1_1911 72 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 206 (accept_3_2 70 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 206
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 206 (accept_3_2 67 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 206 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 206 (accept_3_2 64 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 206
  (Polychromatic418967fa.accept_13_10_12_11_1_731 62 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 129 206 (accept_3_2 61 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 206 (accept_3_2 58 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 206
  (Polychromatic418967fa.accept_20_17_9_6_1_6219 57 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 129 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 206 (accept_3_2 55 129 206 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 206 (accept_3_2 52 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 206 (accept_3_2 49 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 206 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 206 (accept_3_2 46 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 206 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 206 (Polychromatic418967fa.accept_19_6_15_16_1_7972 44 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 206 (accept_3_2 43 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 206 (accept_3_2 40 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 206 (accept_3_2 37 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 206 (Polychromatic418967fa.accept_13_10_12_11_1_731 36 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 206 (accept_3_2 34 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 206 (accept_3_2 31 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 206 (accept_3_2 28 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 206 (Polychromatic418967fa.accept_27_26_21_17_1_12034 26 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 206 (accept_3_2 25 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 206 (accept_3_2 22 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 206 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 206 (accept_3_2 19 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 206 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 206 (accept_3_2 16 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 206 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 206 (accept_3_2 13 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 206 (Polychromatic418967fa.accept_17_12_10_2_1_5835 12 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 206
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 206 (accept_3_2 10 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 206 (Polychromatic418967fa.accept_18_9_3_8_1_5419 9 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 206 (Polychromatic418967fa.accept_17_8_10_2_1_4546 8 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 206 (accept_3_2 7 129 206 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 206 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 129 206
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 206
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 206 (accept_3_2 4 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 206 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 206 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 206 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 206 (accept_3_2 1 129 206 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 206))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_206_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


