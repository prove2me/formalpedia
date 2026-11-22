-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch207
-- name    : Polychromatic418967fa_Branch207
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:22.05812+00:00
-- url     : https://prove2.me/theorems/e80c7b15-c5fa-4b07-a563-0ea07ef267bb
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch207_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_207 : allB 207 207 :=
  allB_succ' 2 206 207 (Eq.refl Bool.true) (allA_succ_of_accept 1 206 207 (accept_3_4 1 206 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 206 207)) (allB_succ' 3 205 207 (Eq.refl Bool.true) (allA_succ_of_accept 2 205 207
  (accept_3_5 2 205 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 207
  (Polychromatic418967fa.accept_19_1_15_17_1_701 1 205 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 205 207))) (allB_succ' 4 204 207 (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 207 3 1 68 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 204 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 204 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 204 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 204 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 204 207)))) (allB_succ' 5 203 207 (Eq.refl Bool.true) (allA_succ_of_accept 4
  203 207 (accept_3_4 4 203 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 207
  (Polychromatic418967fa.accept_14_3_7_11_1_765 3 203 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 203 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 203 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 207 (accept_3_4 1 203 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 203 207))))) (allB_succ' 6 202 207 (Eq.refl Bool.true) (allA_succ_of_accept 5 202 207
  (accept_3_5 5 202 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 202 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 4 202 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 202 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 202 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 207 (accept_3_5 2 202 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 202 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 202 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 207)))))) (allB_succ' 7 201 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 201 207 3 2 67 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 201 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 201 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 201 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 201 207 3 1 67 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 201 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 207))))))) (allB_succ' 8 200 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 200 207 (accept_3_4 7 200 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  200 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 200 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 200 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 200 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 200 207 (accept_3_4 4 200 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 207 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 200 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 207
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 200 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 207 (accept_3_4 1 200 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  207)))))))) (allB_succ' 9 199 207 (Eq.refl Bool.true) (allA_succ_of_accept 8 199 207 (accept_3_5 8 199 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 199
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 199 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 207 (accept_3_5 5 199 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 199 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 199 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 207 (accept_3_5 2 199 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 199 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 207))))))))) (allB_succ' 10 198 207 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 198 207 9 1 22 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 198 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 198 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 207 (Polychromatic418967fa.accept_15_7_3_12_1_365
  7 198 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 207 3 2 66 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 198 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 198 207 3 1 66 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 198 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 198 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 198 207)))))))))) (allB_succ' 11 197 207 (Eq.refl Bool.true) (allA_succ_of_accept 10 197 207 (accept_3_4 10
  197 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 197 207
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 197 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 197 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 197 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 207 (accept_3_4 7 197 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 197 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  197 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 207 (accept_3_4 4 197
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 197 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 197 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 207 (accept_3_4 1 197 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 197 207))))))))))) (allB_succ' 12 196 207 (Eq.refl Bool.true) (allA_succ_of_accept 11 196 207
  (accept_3_5 11 196 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 196 207
  (Polychromatic418967fa.accept_17_10_9_3_1_7144 10 196 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 196 207 (Polychromatic418967fa.accept_19_9_6_17_1_3880 9 196 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 196 207 (accept_3_5 8 196 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 196 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 196 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 196 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  196 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 196 207 (accept_3_5 5 196
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 207
  (Polychromatic418967fa.accept_15_4_1_12_1_914 4 196 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 196 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 196 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 207 (accept_3_5 2 196 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 196 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 207)))))))))))) (allB_succ' 13 195 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 195 207 3 4 65 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 195 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 11 195 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10
  195 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 195 207 3 3 65 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 195 207
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 195 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 195 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 207 3 2 65 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 195 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 195 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 207 3 1 65 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 195 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 207 (Polychromatic418967fa.accept_20_1_15_7_1_3405 1 195
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 207))))))))))))) (allB_succ' 14 194 207
  (Eq.refl Bool.true) (allA_succ_of_accept 13 194 207 (accept_3_4 13 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 194 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 194 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 194 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 194 207 (accept_3_4 10 194 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 194 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  194 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 194 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 194 207 (accept_3_4 7 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 207 (accept_3_4 4 194 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 194 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 207 (accept_3_4 1 194 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  207)))))))))))))) (allB_succ' 15 193 207 (Eq.refl Bool.true) (allA_succ_of_accept 14 193 207 (accept_3_5 14 193 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 207
  (Polychromatic418967fa.accept_21_13_4_18_1_7553 13 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 193 207 (Polychromatic418967fa.accept_19_12_3_17_1_5182 12 193 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 207 (accept_3_5 11 193 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 193 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 207 (accept_3_5 8 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 207 (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 193 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 207 (accept_3_5 5 193 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 207
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 207 (accept_3_5 2 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 1 193 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 207))))))))))))))) (allB_succ' 16 192 207 (Eq.refl Bool.true) (allA_succ_of_gcd 15 192 207 3
  5 64 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 192
  207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 192 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 192 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 207 3 4 64 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 192 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 192 207 (Polychromatic418967fa.accept_18_10_12_9_1_2012 10 192 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 192 207 3 3 64 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 192 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 192 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 192 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 192 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 207 3 2 64 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 5 192 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 4 192 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 192 207 3 1 64 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 192 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 192 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 207)))))))))))))))) (allB_succ' 17 191 207
  (Eq.refl Bool.true) (allA_succ_of_accept 16 191 207 (accept_3_4 16 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 191 207 (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 191 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14
  191 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 191 207 (accept_3_4 13
  191 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 191 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 191 207 (Polychromatic418967fa.accept_24_11_23_15_1_12139 11 191 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 207 (accept_3_4 10 191 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 191 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 207 (accept_3_4 7 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 191 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 207 (accept_3_4 4 191 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 191 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 207 (accept_3_4 1 191 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  207))))))))))))))))) (allB_succ' 18 190 207 (Eq.refl Bool.true) (allA_succ_of_accept 17 190 207 (accept_3_5 17 190 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 190 207
  (Polychromatic418967fa.accept_25_16_15_7_1_12138 16 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 190 207 (Polychromatic418967fa.accept_18_15_10_9_1_2009 15 190 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 190 207 (accept_3_5 14 190 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 190 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 190 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 190 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 190 207 (accept_3_5 11 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 190 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 190 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 190 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 207 (accept_3_5 8 190 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 190 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 190 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 6 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 190 207 (accept_3_5 5 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  190 207 (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 190 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 190 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 190 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 207 (accept_3_5 2 190 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 190 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 207)))))))))))))))))) (allB_succ' 19 189 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 189 207 9 2 21 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 189 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 189 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 207
  (Polychromatic418967fa.accept_19_16_18_17_1_6570 16 189 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 189 207 3 5 63 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 189 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 189 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 207
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 189 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 207 3 4 63 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 189 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 189 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 207 9 1 21 23 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 207
  (Polychromatic418967fa.accept_10_8_9_7_1_1118 8 189 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 189 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 207 3 2 63 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 189 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 207
  (Polychromatic418967fa.accept_11_4_2_9_1_496 4 189 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 207 3 1 63 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 189 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 207))))))))))))))))))) (allB_succ' 20 188
  207 (Eq.refl Bool.true) (allA_succ_of_accept 19 188 207 (accept_3_4 19 188 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 188 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 188 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 188 207 (accept_3_4 16
  188 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 188 207
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 188 207 (Polychromatic418967fa.accept_21_14_20_18_1_9174 14 188 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 207 (accept_3_4 13 188 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 188 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 207 (accept_3_4 10 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 207 (Polychromatic418967fa.accept_16_8_12_15_1_2005 8 188 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 207 (accept_3_4 7 188 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 188 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 207 (accept_3_4 4 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 188 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 188 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 207 (accept_3_4 1 188 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 207)))))))))))))))))))) (allB_succ' 21 187 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 20 187 207 (accept_3_5 20 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 207 (Polychromatic418967fa.accept_13_6_5_12_1_307 19 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 187 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 207 (accept_3_5 17 187 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 187 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 207 (accept_3_5 14 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 187 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 207 (accept_3_5 11 187 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 187 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 207 (accept_3_5 8 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 207 (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 187 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 207 (accept_3_5 5 187 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 207
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 207 (accept_3_5 2 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 187 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 207))))))))))))))))))))) (allB_succ' 22 186 207 (Eq.refl Bool.true) (allA_succ_of_gcd 21 186
  207 3 7 62 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  186 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 186 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 186 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 186 207 3 6 62 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 186 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 186 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 186 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 186 207 3 5 62 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 186 207 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 207 3 4 62 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 11 186 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 207 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 186
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 186 207 3 3 62 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 186 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 207 (Polychromatic418967fa.accept_13_7_4_12_1_1341 7 186 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 207 3 2 62 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 207
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 186 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 186 207 3 1 62 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 186 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 186 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 207)))))))))))))))))))))) (allB_succ' 23
  185 207 (Eq.refl Bool.true) (allA_succ_of_accept 22 185 207 (accept_3_4 22 185 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 207 (accept_3_4 19 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 207 (Polychromatic418967fa.accept_13_4_3_12_1_2066 17 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 207 (accept_3_4 16 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 185 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 207 (accept_3_4 13 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 207 (Polychromatic418967fa.accept_19_11_14_17_1_6607 11 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 207 (accept_3_4 10 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 185 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 207 (accept_3_4 7 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 207 (Polychromatic418967fa.accept_19_5_14_17_1_6550 5 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 207 (accept_3_4 4 185 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 185 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 207 (accept_3_4 1 185 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  207))))))))))))))))))))))) (allB_succ' 24 184 207 (Eq.refl Bool.true) (allA_succ_of_gcd 23 184 207 23 1 8 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 22 184 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 184 207 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 184 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 207 (accept_3_5 20 184 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 184 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 184 207 (accept_3_5 17
  184 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 184 207
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 16 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 184 207 (Polychromatic418967fa.accept_17_15_14_3_1_5947 15 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 207 (accept_3_5 14 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 207 (accept_3_5 11 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 207 (Polychromatic418967fa.accept_14_9_2_11_1_780 9 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 207 (accept_3_5 8 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 207 (accept_3_5 5 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800 4 184 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 207 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 207 (accept_3_5 2 184 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 207)))))))))))))))))))))))) (allB_succ' 25 183 207
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 183 207 3 8 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 183 207 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 183 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 207
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 183 207 3 7 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 183 207 (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 183 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 183 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 207 3 6 61 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 207 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 183 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 183 207 3 5 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 183 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110
  14 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 207
  (Polychromatic418967fa.accept_11_2_7_9_1_890 13 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 183 207 3 4 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 183 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 183 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 183 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 207 3 3 61 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 207
  (Polychromatic418967fa.accept_13_8_1_12_1_762 8 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 183 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 207 3 2 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 183 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 207
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 183 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 183 207 3 1 61 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 183 207 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 183 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 207 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 183 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 207))))))))))))))))))))))))) (allB_succ' 26
  182 207 (Eq.refl Bool.true) (allA_succ_of_accept 25 182 207 (accept_3_4 25 182 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 182 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 182 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 182 207 (accept_3_4 22 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 182 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 182 207 (Polychromatic418967fa.accept_15_5_2_12_1_2543 20 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 207 (accept_3_4 19 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 182 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 182
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 182 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 182 207 (accept_3_4 16 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 182 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 182 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 14 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 182 207 (accept_3_4 13 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 182 207 (Polychromatic418967fa.accept_20_12_2_7_1_4788 12 182
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 182 207 (accept_3_4 10 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  182 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 182 207 (Polychromatic418967fa.accept_17_8_12_3_1_5927 8 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 207 (accept_3_4 7 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 182 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 182 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 182 207 (accept_3_4 4 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  182 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 182 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 182 207 (Polychromatic418967fa.accept_27_2_20_18_1_12131 2 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 207 (accept_3_4 1 182 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 182 207)))))))))))))))))))))))))) (allB_succ' 27 181 207 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 181 207 (accept_3_5 26 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 207 (Polychromatic418967fa.accept_21_4_13_18_1_137 25 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 207 (accept_3_5 23 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 181 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 207
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 207 (accept_3_5 20 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 207 (accept_3_5 17 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 207
  (Polychromatic418967fa.accept_19_15_10_17_1_3859 15 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 181 207 (accept_3_5 14 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 181 207 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 207 (Polychromatic418967fa.accept_7_5_6_4_1_117
  12 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 207 (accept_3_5 11
  181 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 181 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 181 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 207 (accept_3_5 8 181 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 181 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 181 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6
  181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 207 (accept_3_5 5 181
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 207 (Polychromatic418967fa.accept_6_4_1_3_1_77
  4 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 207 (accept_3_5 2 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 207 (Polychromatic418967fa.accept_16_1_5_15_1_2918 1 181 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 207))))))))))))))))))))))))))) (allB_succ' 28 180 207 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 180 207 9 3 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 180 207 (Polychromatic418967fa.accept_17_9_10_3_1_3423 26 180 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 207 (Polychromatic418967fa.accept_19_6_9_17_1_5214 25 180
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 180 207 3 8 60 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 180 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 180 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 180 207 3 7 60 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 180 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 207 9 2 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 180 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 207 (Polychromatic418967fa.accept_7_2_5_4_1_115
  16 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 180 207 3 5 60 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 207
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 14 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 180 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 180 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 207 3 4 60 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 207
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 180 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 10 180 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 180 207 9 1 20 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 180 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 8
  180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 207
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 7 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 207 3 2 60 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 207 (Polychromatic418967fa.accept_16_5_4_15_1_1102 5 180 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 180 207 (Polychromatic418967fa.accept_13_4_11_12_1_1318 4 180
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 207 3 1 60 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 180 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 207)))))))))))))))))))))))))))) (allB_succ' 29 179 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 179 207 (accept_3_4 28 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 179 207 (Polychromatic418967fa.accept_16_11_3_15_1_1989 27 179 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26
  179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 207 (accept_3_4 25
  179 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 23 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 207 (accept_3_4 22 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 179
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 207 (accept_3_4 19 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 207 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 207 (accept_3_4 16 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 15 179
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 207 (accept_3_4 13 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 207 (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 207 (accept_3_4 10 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 179 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 207 (accept_3_4 7 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 6 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 207 (Polychromatic418967fa.accept_21_5_11_18_1_1789 5 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 207 (accept_3_4 4 179 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 207 (Polychromatic418967fa.accept_19_3_8_17_1_5213 3 179
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 207 (accept_3_4 1 179 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  207))))))))))))))))))))))))))))) (allB_succ' 30 178 207 (Eq.refl Bool.true) (allA_succ_of_accept 29 178 207
  (accept_3_5 29 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 28 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 178 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 178 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 178 207 (accept_3_5 26 178 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 178 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 178 207
  (Polychromatic418967fa.accept_19_5_7_17_1_9442 24 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 178 207 (accept_3_5 23 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 207 (accept_3_5 20 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 178 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 18 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 207 (accept_3_5 17 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 207 (accept_3_5 14 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 207
  (Polychromatic418967fa.accept_16_12_2_15_1_490 12 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 207 (accept_3_5 11 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 207 (Polychromatic418967fa.accept_13_10_9_12_1_2814 10 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 207 (accept_3_5 8 178 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 178 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 207 (accept_3_5 5 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 4 178 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 3 178 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 207 (accept_3_5 2 178 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 207))))))))))))))))))))))))))))))
  (allB_succ' 31 177 207 (Eq.refl Bool.true) (allA_succ_of_gcd 30 177 207 3 10 59 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 177 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 207 (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 177 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 207 3 9 59 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 207 3 8 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 207 3 7 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 177 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 207 3 6 59 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 207 (Polychromatic418967fa.accept_14_2_9_11_1_3054 16 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 207 3 5 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 207 3 4 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 207 3 3 59 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 207
  (Polychromatic418967fa.accept_16_8_1_15_1_1982 8 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 207 3 2 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 177 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 207
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 4 177 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 207 3 1 59 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 177 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 207)))))))))))))))))))))))))))))))
  (allB_succ' 32 176 207 (Eq.refl Bool.true) (allA_succ_of_accept 31 176 207 (accept_3_4 31 176 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 176 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 176 207 (accept_3_4 28 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 176 207 (Polychromatic418967fa.accept_25_2_1_7_1_12137 27 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 176 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 176 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 176 207 (accept_3_4 25 176 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 176 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 176 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 176 207 (accept_3_4 22 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 176 207 (Polychromatic418967fa.accept_10_1_6_7_1_710 21 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 176 207 (Polychromatic418967fa.accept_24_20_8_15_1_12136 20 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 207 (accept_3_4 19 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 176 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 207 (accept_3_4 16 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 207 (Polychromatic418967fa.accept_19_15_5_17_1_8036 15 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 207 (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 207 (accept_3_4 13 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 176 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 176 207 (accept_3_4 10 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  176 207 (Polychromatic418967fa.accept_17_9_6_3_1_2398 9 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 176 207 (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 207 (accept_3_4 7 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 176 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 176 207 (accept_3_4 4 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  176 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 176 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 176 207 (Polychromatic418967fa.accept_19_2_5_17_1_3850 2 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 207 (accept_3_4 1 176 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 176 207)))))))))))))))))))))))))))))))) (allB_succ' 33 175 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 175 207 (accept_3_5 32 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 175 207 (Polychromatic418967fa.accept_13_5_6_12_1_2750 31 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 175
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 207 (accept_3_5 29 175
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 175 207 (Polychromatic418967fa.accept_19_8_4_17_1_9510 27 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 207 (accept_3_5 26 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 175 207 (Polychromatic418967fa.accept_17_8_5_3_1_2397 25 175 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 207
  (Polychromatic418967fa.accept_14_10_7_11_1_3015 24 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 175 207 (accept_3_5 23 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 175 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 207 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 175
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 207 (accept_3_5 20 175
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 207
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 19 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 207 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 207 (accept_3_5 17 175 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 207
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 15 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 207 (accept_3_5 14 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 207 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 175 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 207 (accept_3_5 11 175 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 175 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 207 (accept_3_5 8 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 207 (Polychromatic418967fa.accept_13_7_6_12_1_2027 7 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 207 (Polychromatic418967fa.accept_15_6_10_12_1_2538 6 175 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 207 (accept_3_5 5 175 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 207 (accept_3_5 2 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 207 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 175 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 207))))))))))))))))))))))))))))))))) (allB_succ' 34 174 207 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 174 207 3 11 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 174 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 32 174 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 174 207 3 10 58 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 174 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 174 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 174 207 3 9 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 174 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 26
  174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 207 3 8 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 174
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 174 207 3 7 58 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 174 207
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 207 3 6 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 174 207 3 5 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 174 207 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 207 3 4 58 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 207
  (Polychromatic418967fa.accept_10_1_4_7_1_374 11 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 174 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 207 3 3 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 207 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 174 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 207
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 7 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 207 3 2 58 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 207 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 174 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 174 207 3 1 58 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 174 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 174 207)))))))))))))))))))))))))))))))))) (allB_succ' 35 173 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 173 207 (accept_3_4 34 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 173 207 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 173 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 173 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 207 (accept_3_4 31 173 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 29 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 173 207 (accept_3_4 28 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 173 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 173 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 173 207 (accept_3_4 25 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 173 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 173 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 173 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 173 207 (accept_3_4 22 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 173 207 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 173 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 207 (accept_3_4 19 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 207
  (Polychromatic418967fa.accept_33_17_8_9_1_12135 17 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 173 207 (accept_3_4 16 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 173 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 173 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 207 (accept_3_4 13 173 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 207
  (Polychromatic418967fa.accept_16_12_13_15_1_1966 12 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 207 (Polychromatic418967fa.accept_13_11_4_12_1_3585 11 173 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 207 (accept_3_4 10 173 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 173 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 207
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 207 (accept_3_4 7 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 5 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 207 (accept_3_4 4 173 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 207 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 173 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 207 (accept_3_4 1 173 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  207))))))))))))))))))))))))))))))))))) (allB_succ' 36 172 207 (Eq.refl Bool.true) (allA_succ_of_accept 35 172 207
  (accept_3_5 35 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 207
  (Polychromatic418967fa.accept_10_4_2_7_1_373 34 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 172 207 (Polychromatic418967fa.accept_15_3_7_12_1_372 33 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 172 207 (accept_3_5 32 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 172 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 172 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 207 (accept_3_5 29
  172 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 207
  (Polychromatic418967fa.accept_13_2_3_12_1_735 28 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 172 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 172 207 (accept_3_5 26 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 172 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 172 207 (Polychromatic418967fa.accept_10_4_2_7_1_373
  24 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 207 (accept_3_5 23
  172 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 207
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 22 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 172 207 (Polychromatic418967fa.accept_14_7_4_11_1_3038 21 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 207 (accept_3_5 20 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 172 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 207 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 207 (accept_3_5 17
  172 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 207
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 172 207 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 207 (accept_3_5 14 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 172 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 207
  (Polychromatic418967fa.accept_18_12_10_9_1_5497 12 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 172 207 (accept_3_5 11 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 172 207 (Polychromatic418967fa.accept_15_10_7_12_1_2490 10 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 207 (Polychromatic418967fa.accept_10_9_2_7_1_1096
  9 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 207 (accept_3_5 8
  172 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 207
  (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 172 207 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 207 (accept_3_5 5 172 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 172 207 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 172 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3
  172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 207 (accept_3_5 2 172
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 207 (Polychromatic418967fa.accept_6_1_4_3_1_14
  1 172 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172
  207)))))))))))))))))))))))))))))))))))) (allB_succ' 37 171 207 (Eq.refl Bool.true) (allA_succ_of_gcd 36 171 207 9 4 19
  23 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 207
  (Polychromatic418967fa.accept_14_7_3_11_1_2199 35 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 207 3 11 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802
  32 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 207
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 31 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 171 207 3 10 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 171 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 171 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 207 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 207 9 3 19 23
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 26 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 207 (Polychromatic418967fa.accept_11_3_6_9_1_1378 25 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 171 207 3 8 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 171 207
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 23 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 171 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 207 3 7 57 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 207 (Polychromatic418967fa.accept_13_6_2_12_1_2802 19 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 207 9 2 19 23 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 207 (Polychromatic418967fa.accept_13_4_2_12_1_2800
  17 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 207
  (Polychromatic418967fa.accept_10_6_1_7_1_342 16 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 207 3 5 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 207 (Polychromatic418967fa.accept_10_4_1_7_1_371 14 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 171 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 207 3 4 57 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 207
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 11 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 207 (Polychromatic418967fa.accept_13_10_2_12_1_1332 10 171 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 207 9 1 19 23 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 207 (Polychromatic418967fa.accept_14_7_3_11_1_2199 7 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 207 3 2 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 207 (Polychromatic418967fa.accept_13_5_2_12_1_1301 5 171 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 207
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 171 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 207 3 1 57 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 207 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 171 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 171 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 207)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 170 207 (Eq.refl Bool.true) (allA_succ_of_accept 37 170 207 (accept_3_4 37 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 170 207 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 170 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 170 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 170 207 (accept_3_4 34 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 170 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 170 207 (Polychromatic418967fa.accept_15_2_5_12_1_369 32 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 170 207 (accept_3_4 31 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 170 207 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 170
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 170 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 170 207 (accept_3_4 28 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 170 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 170 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 170 207 (accept_3_4 25 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 170 207 (Polychromatic418967fa.accept_13_11_1_12_1_742 24 170 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 170 207 (accept_3_4 22 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 170 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 170 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 170 207 (accept_3_4 19 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 207 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 170 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 170 207 (accept_3_4 16 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 170 207 (Polychromatic418967fa.accept_13_2_1_12_1_1326 15 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 170 207 (Polychromatic418967fa.accept_16_14_10_15_1_3969 14 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 207 (accept_3_4 13 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 170 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 207
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 170 207 (accept_3_4 10 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  170 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 170 207 (Polychromatic418967fa.accept_13_8_1_12_1_762 8 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 207 (accept_3_4 7 170 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 170 207
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 170 207 (accept_3_4 4 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  170 207 (Polychromatic418967fa.accept_18_3_8_9_1_1956 3 170 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 170 207 (Polychromatic418967fa.accept_13_2_1_12_1_1326 2 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 207 (accept_3_4 1 170 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 170 207)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 169 207
  (Eq.refl Bool.true) (allA_succ_of_accept 38 169 207 (accept_3_5 38 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 169 207 (Polychromatic418967fa.accept_15_7_4_12_1_2530 37 169 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 169 207 (Polychromatic418967fa.accept_20_16_9_7_1_3402 36 169
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 207 (accept_3_5 35 169
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 169 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 169 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 169 207 (accept_3_5 32 169 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 169 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 169 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 207 (accept_3_5 29
  169 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 207
  (Polychromatic418967fa.accept_6_4_1_3_1_77 28 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 169 207 (Polychromatic418967fa.accept_22_5_15_9_1_10649 27 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 169 207 (accept_3_5 26 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 169 207 (Polychromatic418967fa.accept_20_5_9_7_1_10766 25 169 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 207
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 169 207 (accept_3_5 23 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 207 (accept_3_5 20 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 207 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 169 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 207 (accept_3_5 17 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 207 (Polychromatic418967fa.accept_21_15_1_18_1_3066 15 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 207 (accept_3_5 14 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 207 (Polychromatic418967fa.accept_11_2_4_9_1_484 13 169
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 207
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 207 (accept_3_5 11 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 207 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 207 (accept_3_5 8 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 207 (Polychromatic418967fa.accept_15_7_4_12_1_2530 7 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 207 (accept_3_5 5 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 207 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 207 (accept_3_5 2 169 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 207 (Polychromatic418967fa.accept_15_1_4_12_1_2401 1 169 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 207)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 168 207 (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 207 3 13 56 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 168 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 168 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 37 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 207 3 12 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174
  35 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 168 207
  (Polychromatic418967fa.accept_26_8_12_25_1_12134 34 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 168 207 3 11 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 168 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 32 168 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 207
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 31 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 168 207 3 10 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 168 207 (Polychromatic418967fa.accept_10_9_8_7_1_714 29 168 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 168 207
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 168 207 3 9 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 168 207 (Polychromatic418967fa.accept_18_8_6_9_1_5576 26 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 168
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 207 3 8 56 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 22 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 207 3 7 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 207 (Polychromatic418967fa.accept_16_4_8_15_1_1113
  20 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 207
  (Polychromatic418967fa.accept_10_9_8_7_1_714 19 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 207 3 6 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 207 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 207 (Polychromatic418967fa.accept_26_16_12_25_1_12133 16
  168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 207 3 5 56 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 168 207
  (Polychromatic418967fa.accept_17_14_15_3_1_4618 14 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 168 207 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 168 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 207 3 4 56 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 207
  (Polychromatic418967fa.accept_22_11_14_9_1_12079 11 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 168 207 (Polychromatic418967fa.accept_20_10_8_7_1_7834 10 168 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 207 3 3 56 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 207
  (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 168 207 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 207 3 2 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 207 (Polychromatic418967fa.accept_10_5_8_7_1_2174 5 168 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 207
  (Polychromatic418967fa.accept_16_4_8_15_1_1113 4 168 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 168 207 3 1 56 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 168 207 (Polychromatic418967fa.accept_15_2_3_12_1_891 2 168 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 207 (Polychromatic418967fa.accept_16_1_8_15_1_1945 1 168
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168
  207)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 167 207 (Eq.refl Bool.true) (allA_succ_of_accept 40 167 207
  (accept_3_4 40 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 207
  (Polychromatic418967fa.accept_19_1_15_17_1_701 39 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 167 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 207 (accept_3_4 37 167 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 167 207 (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 167 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 207
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 207 (accept_3_4 34 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 207 (accept_3_4 31 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 167 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 207
  (Polychromatic418967fa.accept_11_7_2_9_1_480 29 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 207 (accept_3_4 28 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 207 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 207 (accept_3_4 25 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 167 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 207
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 207 (accept_3_4 22 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 207 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 207 (accept_3_4 19 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 207 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 167 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 207
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 207 (accept_3_4 16 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 207 (Polychromatic418967fa.accept_11_4_2_9_1_496 15 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 207 (accept_3_4 13 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 207 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 167 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 207
  (Polychromatic418967fa.accept_16_11_7_15_1_1998 11 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 167 207 (accept_3_4 10 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 167 207 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 167 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 207 (accept_3_4 7 167 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 207 (Polychromatic418967fa.accept_15_6_2_12_1_885
  6 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 207
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 207 (accept_3_4 4 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 207 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 167 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 207 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 207 (accept_3_4 1 167 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 207))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 166 207 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 207 (accept_3_5 41 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 166 207 (Polychromatic418967fa.accept_19_2_14_17_1_700 40 166 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 166 207 (Polychromatic418967fa.accept_16_7_6_15_1_495 39 166
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 207 (accept_3_5 38 166
  207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 207
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 207 (accept_3_5 35 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 207 (accept_3_5 32 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 166 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 207
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 207 (accept_3_5 29 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 207 (Polychromatic418967fa.accept_13_2_10_12_1_757 28 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 207 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 207 (accept_3_5 26 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 207
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 166 207 (accept_3_5 23 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 166 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 166 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 207 (accept_3_5 20 166 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 207
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 207 (accept_3_5 17 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 207 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 207 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 207 (accept_3_5 14 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 207
  (Polychromatic418967fa.accept_18_12_4_9_1_5452 12 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 207 (accept_3_5 11 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 207 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 207 (accept_3_5 8 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 207 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 166 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 207
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 207 (accept_3_5 5 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 207 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 166 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 207 (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 207 (accept_3_5 2 166 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 207 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 207))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 165 207 (Eq.refl Bool.true) (allA_succ_of_gcd 42 165 207 3 14 55 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 207 (Polychromatic418967fa.accept_24_16_21_15_1_6954 40 165 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 165 207 3 13 55 69 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 207 3 12 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 165 207 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 165 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 165 207 3 11 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 165 207 (Polychromatic418967fa.accept_10_2_5_7_1_1124 32 165 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 207
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 165 207 3 10 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 165 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 165 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 207 (Polychromatic418967fa.accept_10_8_5_7_1_358
  28 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 165 207 3 9 55 69
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 25 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 207 3 8 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 207 (Polychromatic418967fa.accept_10_3_5_7_1_330
  23 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 207
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 207 3 7 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 165 207 (Polychromatic418967fa.accept_16_4_5_15_1_5083 20 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 165
  207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 207 3 6 55 69 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 207
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 207 (Polychromatic418967fa.accept_13_3_9_12_1_2062 16 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 207 3 5 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 207
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 207 3 4 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 207 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 207 3 3 55 69 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 207
  (Polychromatic418967fa.accept_10_8_5_7_1_358 8 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 207 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 207 3 2 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 207 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 165 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 207
  (Polychromatic418967fa.accept_16_4_5_15_1_5083 4 165 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 207 3 1 55 69 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 207 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 207 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 165 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  207))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 164 207 (Eq.refl Bool.true) (allA_succ_of_accept 43 164
  207 (accept_3_4 43 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 164 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 164 207 (accept_3_4 40 164 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 164 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 164 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 164 207
  (Polychromatic418967fa.accept_25_13_14_7_1_12117 38 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 164 207 (accept_3_4 37 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 164 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 164 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 164 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 164 207 (accept_3_4 34 164 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 164 207 (Polychromatic418967fa.accept_10_3_4_7_1_353
  33 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 164 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 32 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 164 207 (accept_3_4 31 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 164 207 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 164 207 (accept_3_4 28 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 164 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 164 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 164 207
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 26 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 164 207 (accept_3_4 25 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 164 207 (Polychromatic418967fa.accept_15_9_14_12_1_913 24 164 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 164 207 (accept_3_4 22 164 207
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 164 207 (Polychromatic418967fa.accept_10_1_4_7_1_374
  21 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 164 207
  (Polychromatic418967fa.accept_7_6_3_4_1_294 20 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 164 207 (accept_3_4 19 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 164 207 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 207 (accept_3_4 16 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 207 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 164 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 164 207
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 14 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 164 207 (accept_3_4 13 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 164 207 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 207 (accept_3_4 10 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 207 (Polychromatic418967fa.accept_13_9_8_12_1_2031 9 164 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 164 207
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 164 207 (accept_3_4 7 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 207 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 207 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 207 (accept_3_4 4 164 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 207 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 164 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 207
  (Polychromatic418967fa.accept_10_2_4_7_1_352 2 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 207 (accept_3_4 1 164 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  207)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 163 207 (Eq.refl Bool.true) (allA_succ_of_accept 44 163
  207 (accept_3_5 44 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 163 207
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 43 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 163 207 (Polychromatic418967fa.accept_18_6_1_9_1_5551 42 163 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 207 (accept_3_5 41 163 207 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 207
  (Polychromatic418967fa.accept_16_7_3_15_1_2940 39 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 207 (accept_3_5 38 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 207 (Polychromatic418967fa.accept_13_11_7_12_1_2758 37 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 207 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 207 (accept_3_5 35 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 207
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 207 (accept_3_5 32 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 31 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 207 (Polychromatic418967fa.accept_13_4_7_12_1_2823 30 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 207 (accept_3_5 29 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 207
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 207 (accept_3_5 26 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 207 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 207 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 207 (accept_3_5 23 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 163 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 207 (accept_3_5 20 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 207 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 207 (accept_3_5 17 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 207
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 207
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 207 (accept_3_5 14 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 207 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 207 (accept_3_5 11 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 207
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 207 (accept_3_5 8 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 207 (Polychromatic418967fa.accept_16_7_3_15_1_2940 7 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 207 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 207 (accept_3_5 5 163 207 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 207 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 207 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 207
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 207 (accept_3_5 2 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 207 (Polychromatic418967fa.accept_15_1_13_12_1_347 1 163 207 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 207)))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_207_segment_001))))))))))))))))))))))))))))))))))))))))))))


