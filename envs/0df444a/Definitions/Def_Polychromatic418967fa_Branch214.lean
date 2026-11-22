-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch214
-- name    : Polychromatic418967fa_Branch214
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:51.045429+00:00
-- url     : https://prove2.me/theorems/b72df9e6-ccd2-4cad-bbcc-b0d7cd468b00
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch214_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_214 : allB 214 214 :=
  allB_succ' 2 213 214 (Eq.refl Bool.true) (allA_succ_of_accept 1 213 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1
  213 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 214)) (allB_succ' 3 212 214
  (Eq.refl Bool.true) (allA_of_3_1 3 212 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 211 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 211 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 211 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 211 214 (accept_3_3 2 211 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 211 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 211 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 211 214)))) (allB_succ' 5 210 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 210 214 2 2 105 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 210 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 214 2 1 105 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 1 210 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 210 214))))) (allB_succ' 6 209 214 (Eq.refl Bool.true) (allA_of_3_1 6 209 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 7 208 214 (Eq.refl Bool.true) (allA_succ_of_gcd 6 208 214 2 3 104 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 208 214 (accept_3_3 5 208 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 208 214 2 2 104 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 208 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 3 208 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 208 214 2 1 104 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 208 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 208 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 214))))))) (allB_succ' 8 207 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 207 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 207 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 6 207 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 214 (accept_3_3 5 207 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 214
  (Polychromatic418967fa.accept_22_4_9_16_1_12651 4 207 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 207 214 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 207 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 207 214 (accept_3_3 2 207 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 207 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 207 214)))))))) (allB_succ' 9 206 214 (Eq.refl Bool.true)
  (allA_of_3_1 9 206 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 205 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 205 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 205 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 214 (accept_3_3 8 205 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 205 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 205 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 6
  205 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 205 214 (accept_3_3 5 205
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 205 214
  (Polychromatic418967fa.accept_12_4_1_10_1_221 4 205 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 205 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 214 (accept_3_3 2 205 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 205 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 205 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 214)))))))))) (allB_succ' 11 204 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 204 214 2 5 102 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 204 214 (Polychromatic418967fa.accept_19_9_14_5_1_1890 9 204 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 214 2 4 102 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 214
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 204 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 204 214 2 3 102 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 204 214 (accept_3_3 5 204 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 214 2 2 102 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 204 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 204 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 214 2 1 102 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 1 204 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 214))))))))))) (allB_succ' 12 203 214 (Eq.refl Bool.true) (allA_of_3_1 12 203 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 13 202 214 (Eq.refl Bool.true) (allA_succ_of_gcd 12 202 214 2 6 101 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 202 214 (accept_3_3 11
  202 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 202 214 2 5 101 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 202 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 202 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 202 214 2 4 101 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 202 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 202 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 202 214 2 3 101 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 202 214 (accept_3_3 5 202 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 202 214 2 2 101 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 202 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3
  202 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 214 2 1 101 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 1 202 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 214))))))))))))) (allB_succ' 14 201 214 (Eq.refl Bool.true) (allA_succ_of_accept 13 201 214
  (Polychromatic418967fa.accept_6_1_3_4_1_1 13 201 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 214 (Polychromatic418967fa.accept_19_12_11_5_1_950 12 201 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 214 (accept_3_3 11 201 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 201 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 201 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9
  201 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 214 (accept_3_3 8 201
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 214 (Polychromatic418967fa.accept_4_3_1_2_1_62
  7 201 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 201 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 214 (accept_3_3 5 201 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  201 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 201 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 214 (accept_3_3 2 201 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 201 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 214)))))))))))))) (allB_succ' 15 200 214 (Eq.refl
  Bool.true) (allA_of_3_1 15 200 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 199 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 199 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 214 (accept_3_3 14 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 199 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 199 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 12
  199 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 199 214 (accept_3_3 11
  199 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 214
  (Polychromatic418967fa.accept_13_10_4_6_1_3224 10 199 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 199 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 214 (accept_3_3 8 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 199 214 (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 199 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  199 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 199 214 (accept_3_3 5 199
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 4 199 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 199 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 214 (accept_3_3 2 199 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 199 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 214)))))))))))))))) (allB_succ' 17 198 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 16 198 214 2 8 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 198 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 214 2 7 99 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 198 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 198 214 2 6 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 198 214 (accept_3_3 11 198 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 198 214 2 5 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 198 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 198 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 214 2 4 99 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 214
  (Polychromatic418967fa.accept_15_7_3_4_1_574 7 198 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 214 2 3 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 214 (accept_3_3 5 198 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198
  214 2 2 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  198 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 198 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 198 214 2 1 99 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 198 214 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 198 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 214))))))))))))))))) (allB_succ' 18 197 214 (Eq.refl
  Bool.true) (allA_of_3_1 18 197 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 196 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 18 196 214 2 9 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 196 214 (accept_3_3 17 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 196 214 2 8 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 196 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 196 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 214 2 7 98 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 196 214 2 6 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 196 214 (accept_3_3 11 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 196 214 2 5 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 196 214 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 196 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 214 2 4 98 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 214 2 3 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 214 (accept_3_3 5 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  214 2 2 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 214 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 196 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 214 2 1 98 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 196 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 214))))))))))))))))))) (allB_succ' 20 195 214
  (Eq.refl Bool.true) (allA_succ_of_accept 19 195 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 195 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 214 (accept_3_3 17 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 195 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 195 214 (Polychromatic418967fa.accept_17_15_8_10_1_2886 15 195 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 214 (accept_3_3 14 195 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 195 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 195 214 (accept_3_3 11 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 195 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 195 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 214 (accept_3_3 8 195 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 195 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 195 214 (accept_3_3 5 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  195 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 195 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 195 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 195 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 214 (accept_3_3 2 195 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 214)))))))))))))))))))) (allB_succ' 21 194 214
  (Eq.refl Bool.true) (allA_of_3_1 21 194 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 193 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 21 193 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 214 (accept_3_3 20 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 193 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 193 214
  (Polychromatic418967fa.accept_13_5_11_6_1_505 18 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 193 214 (accept_3_3 17 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 193 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 193 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 214 (accept_3_3 14 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 214 (Polychromatic418967fa.accept_24_13_1_22_1_12650 13 193 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 193 214 (accept_3_3 11 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 214 (accept_3_3 8 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 214 (accept_3_3 5 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 193 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 214 (accept_3_3 2 193 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 193 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 214)))))))))))))))))))))) (allB_succ' 23 192 214
  (Eq.refl Bool.true) (allA_succ_of_gcd 22 192 214 2 11 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 192
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 192 214 2 10 96 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 192 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 214 2 9 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 214 (accept_3_3 17 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 192 214 2 8 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 192 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 192 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 192 214 2 7 96 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 214 2 6 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 214 (accept_3_3 11 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 192 214 2 5 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 192 214 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 192 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 192 214 2 4 96 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 214 2 3 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 214 (accept_3_3 5 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192
  214 2 2 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  192 214 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 192 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 192 214 2 1 96 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 192 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 192 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 214))))))))))))))))))))))) (allB_succ' 24 191 214
  (Eq.refl Bool.true) (allA_of_3_1 24 191 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 190 214 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 190 214 2 12 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 190 214 (accept_3_3 23 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 190 214 2 11 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 190 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 190 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 190 214 2 10 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 214 2 9 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 214 (accept_3_3 17 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 214 2 8 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 190 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 190 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 190 214 2 7 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 214 2 6 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 214 (accept_3_3 11 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 214 2 5 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 214 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 190 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 214 2 4 95 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 214
  (Polychromatic418967fa.accept_15_7_10_4_1_151 7 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 214 2 3 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 214 (accept_3_3 5 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  214 2 2 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 190 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 214 2 1 95 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 214 (Polychromatic418967fa.accept_13_1_8_6_1_1016 1 190 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 214))))))))))))))))))))))))) (allB_succ' 26 189 214
  (Eq.refl Bool.true) (allA_succ_of_accept 25 189 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 214
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 214 (accept_3_3 23 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 214 (Polychromatic418967fa.accept_13_9_7_6_1_1673 22 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 189 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 21 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 214 (accept_3_3 20 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 189 214 (accept_3_3 17 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 189 214 (Polychromatic418967fa.accept_24_16_21_22_1_12636 16 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 214 (accept_3_3 14 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 189 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 214
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 12 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 189 214 (accept_3_3 11 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 189 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 189 214 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 189 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 214 (accept_3_3 8 189 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 189 214 (accept_3_3 5 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  189 214 (Polychromatic418967fa.accept_13_4_7_6_1_2359 4 189 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 189 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 214 (accept_3_3 2 189 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 189 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 214)))))))))))))))))))))))))) (allB_succ' 27 188 214
  (Eq.refl Bool.true) (allA_of_3_1 27 188 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 187 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 187 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 214 (accept_3_3 26 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 187 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 187 214
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 187 214 (accept_3_3 23 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 187 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 187 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 214 (accept_3_3 20 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 214 (Polychromatic418967fa.accept_16_3_11_6_1_4467 19 187 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 214
  (Polychromatic418967fa.accept_15_3_7_4_1_1225 18 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 187 214 (accept_3_3 17 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 187 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 187 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 214 (accept_3_3 14 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 187 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 214 (accept_3_3 11 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 214 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 214 (accept_3_3 8 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 214 (Polychromatic418967fa.accept_21_7_19_4_1_4956 7 187 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 214 (accept_3_3 5 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 187 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 214 (accept_3_3 2 187 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 214)))))))))))))))))))))))))))) (allB_succ' 29 186
  214 (Eq.refl Bool.true) (allA_succ_of_gcd 28 186 214 2 14 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 186
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 186 214 2 13 93 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 186 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 214 2 12 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 214 (accept_3_3 23 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 186 214 2 11 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 186 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 186 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 186 214 2 10 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 214 2 9 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 214 (accept_3_3 17 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 186 214 2 8 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 186 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 186 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 186 214 2 7 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 214 2 6 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 214 (accept_3_3 11 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 186 214 2 5 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 186 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 186 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 186 214 2 4 93 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 214
  (Polychromatic418967fa.accept_13_7_4_6_1_3221 7 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 214 2 3 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 214 (accept_3_3 5 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186
  214 2 2 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  186 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 186 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 186 214 2 1 93 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 186 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 186 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 214))))))))))))))))))))))))))))) (allB_succ' 30 185
  214 (Eq.refl Bool.true) (allA_of_3_1 30 185 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 184 214
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 184 214 2 15 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 184 214 (accept_3_3 29 184 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 184 214 2 14 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 184 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 184 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 184 214 2 13 92 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 184 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 184 214 2 12 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 184 214 (accept_3_3 23 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 184 214 2 11 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 184 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 184 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 184 214 2 10 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 184 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 184 214 2 9 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 184 214 (accept_3_3 17 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 214 2 8 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 184 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 184 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 214 2 7 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 184 214 2 6 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 184 214 (accept_3_3 11 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 214 2 5 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 214 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 184 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 214 2 4 92 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 214 2 3 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 214 (accept_3_3 5 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  214 2 2 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 184 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 214 2 1 92 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 184 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 214))))))))))))))))))))))))))))))) (allB_succ' 32
  183 214 (Eq.refl Bool.true) (allA_succ_of_accept 31 183 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 183 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 183 214 (accept_3_3 29 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 183 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 183 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 214 (accept_3_3 26 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 183 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 183 214 (accept_3_3 23 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 183 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 183 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 214 (accept_3_3 20 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 183 214 (accept_3_3 17 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 183 214 (Polychromatic418967fa.accept_13_3_1_6_1_509 16 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 183 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 214 (accept_3_3 14 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 183 214 (accept_3_3 11 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 183 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 183 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 214 (accept_3_3 8 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 6 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 183 214 (accept_3_3 5 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  183 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 183 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 183 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 214 (accept_3_3 2 183 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183 214)))))))))))))))))))))))))))))))) (allB_succ' 33
  182 214 (Eq.refl Bool.true) (allA_of_3_1 33 182 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 181 214
  (Eq.refl Bool.true) (allA_succ_of_accept 33 181 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 181 214 (accept_3_3 32 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 181 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 181 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 181 214 (accept_3_3 29 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 181 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 214 (accept_3_3 26 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 214 (accept_3_3 23 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 214 (accept_3_3 20 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 214
  (Polychromatic418967fa.accept_13_5_12_6_1_508 18 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 214 (accept_3_3 17 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 214 (accept_3_3 14 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 13 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 181 214 (accept_3_3 11 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 181 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 214 (accept_3_3 8 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 214 (accept_3_3 5 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 181 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 214 (accept_3_3 2 181 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 214 (Polychromatic418967fa.accept_16_1_5_6_1_4435 1 181 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 214)))))))))))))))))))))))))))))))))) (allB_succ' 35
  180 214 (Eq.refl Bool.true) (allA_succ_of_gcd 34 180 214 2 17 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 214 (Polychromatic418967fa.accept_19_14_9_5_1_9941 33 180
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 180 214 2 16 90 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 180 214
  (Polychromatic418967fa.accept_13_5_11_6_1_505 31 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 214 2 15 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 214 (accept_3_3 29 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 180 214 2 14 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 180 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 180 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 180 214 2 13 90 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 180 214
  (Polychromatic418967fa.accept_35_25_5_4_1_12649 25 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 180 214 2 12 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 180 214 (accept_3_3 23 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 180 214 2 11 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 180 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 180 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 214 2 10 90 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 214
  (Polychromatic418967fa.accept_16_3_4_6_1_6798 19 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 214 2 9 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 214 (accept_3_3 17 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 214 2 8 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 180 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 180 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 180 214 2 7 90 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 214 2 6 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 214 (accept_3_3 11 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 214 2 5 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 180 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 180 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 180 214 2 4 90 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 214
  (Polychromatic418967fa.accept_19_7_9_5_1_8590 7 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 214 2 3 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 214 (accept_3_3 5 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180
  214 2 2 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  180 214 (Polychromatic418967fa.accept_16_3_4_6_1_6798 3 180 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 180 214 2 1 90 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 180 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 180 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 214))))))))))))))))))))))))))))))))))) (allB_succ'
  36 179 214 (Eq.refl Bool.true) (allA_of_3_1 36 179 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 178 214
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 178 214 2 18 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 178 214 (accept_3_3 35 178 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 178 214 2 17 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 178 214 (Polychromatic418967fa.accept_13_7_9_6_1_148 33 178 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 178 214 2 16 89 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 178 214
  (Polychromatic418967fa.accept_19_12_7_5_1_5725 31 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 178 214 2 15 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 178 214 (accept_3_3 29 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 178 214 2 14 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 178 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 178 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 214 2 13 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 214
  (Polychromatic418967fa.accept_15_10_13_4_1_1210 25 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 178 214 2 12 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 178 214 (accept_3_3 23 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 214 2 11 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 178 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 214 2 10 89 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 214 2 9 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 214 (accept_3_3 17 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 214 2 8 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 178 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 214 2 7 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 214 2 6 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 214 (accept_3_3 11 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 214 2 5 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 178 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 214 2 4 89 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 214
  (Polychromatic418967fa.accept_13_7_9_6_1_148 7 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 214 2 3 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 214 (accept_3_3 5 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  214 2 2 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 214 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 178 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 214 2 1 89 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 178 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 214))))))))))))))))))))))))))))))))))))) (allB_succ'
  38 177 214 (Eq.refl Bool.true) (allA_succ_of_accept 37 177 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 177 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 214
  (Polychromatic418967fa.accept_21_15_9_4_1_2207 36 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 214 (accept_3_3 35 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 214 (accept_3_3 32 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 214 (accept_3_3 29 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 214 (accept_3_3 26 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 214
  (Polychromatic418967fa.accept_13_11_8_6_1_1023 24 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 214 (accept_3_3 23 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 214 (accept_3_3 20 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 214 (accept_3_3 17 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 214 (accept_3_3 14 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 214 (accept_3_3 11 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 214 (Polychromatic418967fa.accept_15_9_12_4_1_2023 9 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 214 (accept_3_3 8 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 214 (accept_3_3 5 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 177 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 214 (accept_3_3 2 177 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 177 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 214))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 176 214 (Eq.refl Bool.true) (allA_of_3_1 39 176 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 175 214 (Eq.refl Bool.true) (allA_succ_of_accept 39 175 214 (Polychromatic418967fa.accept_6_3_1_4_1_25
  39 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 175 214 (accept_3_3 38
  175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 175 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 37 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 175 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 175 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 175 214 (accept_3_3 35 175 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 175 214 (Polychromatic418967fa.accept_19_15_4_5_1_11338 34 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 214 (accept_3_3 32 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 175 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 30 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 175 214 (accept_3_3 29 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 175 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 27 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 175 214 (accept_3_3 26 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 24 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 214 (accept_3_3 23 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 22 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 214 (accept_3_3 20 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 19 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 214 (Polychromatic418967fa.accept_19_18_4_5_1_5723 18 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 214 (accept_3_3 17 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 175
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 15 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 214 (accept_3_3 14 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 12 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 214 (accept_3_3 11 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 214 (accept_3_3 8 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 214 (Polychromatic418967fa.accept_15_7_10_4_1_151 7 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 6 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 214 (accept_3_3 5 175 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 175 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 3 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 214 (accept_3_3 2 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 214)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 174 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 40 174 214 2 20 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 174 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 39 174 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 174 214 2 19 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 174 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 214 2 18 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 214 (accept_3_3 35 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 174 214 2 17 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 174 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 174 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 174 214 2 16 87 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 214 2 15 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 214 (accept_3_3 29 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 174 214 2 14 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 174 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 27 174 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 174 214 2 13 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 214
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 25 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 214 2 12 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 214 (accept_3_3 23 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 174 214 2 11 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 174 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 174 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 174 214 2 10 87 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 214 2 9 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 214 (accept_3_3 17 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 174 214 2 8 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 174 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 174 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 174 214 2 7 87 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 13 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 214 2 6 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 214 (accept_3_3 11 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 214 2 5 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 174 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 174 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 214 2 4 87 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 214 2 3 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 214 (accept_3_3 5 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174
  214 2 2 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  174 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 174 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 174 214 2 1 87 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 174 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 174 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 214)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 173 214 (Eq.refl Bool.true) (allA_of_3_1 42 173 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 172 214 (Eq.refl Bool.true) (allA_succ_of_gcd 42 172 214 2 21 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 172 214 (accept_3_3 41 172 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 172 214 2 20 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 172 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39
  172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 172 214 2 19 86 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 172 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 172 214 2 18 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 172 214 (accept_3_3 35 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 172 214 2 17 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 172 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 172 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 214 2 16 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 214 2 15 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 214 (accept_3_3 29 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 214 2 14 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 172 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 172 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 214 2 13 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 214 2 12 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 214 (accept_3_3 23 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 214 2 11 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 172 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 214 2 10 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 214 2 9 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 172 214 (accept_3_3 17 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 214 2 8 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 172 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 214 2 7 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 214 2 6 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 214 (accept_3_3 11 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 214 2 5 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 214 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 172 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 214 2 4 86 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 214 2 3 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 214 (accept_3_3 5 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  214 2 2 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 172 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 214 2 1 86 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 1 172 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 214)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 171 214 (Eq.refl Bool.true) (allA_succ_of_accept 43 171 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  43 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 171 214 (accept_3_3 41 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 171 214 (Polychromatic418967fa.accept_13_1_2_6_1_515 40 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 171 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 214 (accept_3_3 38 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 171 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 171 214 (accept_3_3 35 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 171 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 214 (accept_3_3 32 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 30 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 171 214 (accept_3_3 29 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 171 214 (Polychromatic418967fa.accept_15_13_6_4_1_1221 28 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 171 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 214 (accept_3_3 26 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 214
  (Polychromatic418967fa.accept_15_9_6_4_1_1220 24 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 171 214 (accept_3_3 23 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 171 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 214 (accept_3_3 20 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 171 214 (accept_3_3 17 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 171 214 (Polychromatic418967fa.accept_23_16_10_7_1_12648 16 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 214 (accept_3_3 14 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 214
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 12 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 214 (accept_3_3 11 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 171 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 214 (accept_3_3 8 171 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 214 (accept_3_3 5 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  171 214 (Polychromatic418967fa.accept_13_4_2_6_1_1043 4 171 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 214 (Polychromatic418967fa.accept_16_3_11_6_1_4467 3 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 214 (accept_3_3 2 171 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  214)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 170 214 (Eq.refl Bool.true) (allA_of_3_1 45 170 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 46 169 214 (Eq.refl Bool.true) (allA_succ_of_accept 45 169 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 45 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 214 (accept_3_3 44 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 214 (Polychromatic418967fa.accept_23_19_8_7_1_2745 42 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 214 (accept_3_3 41 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 169 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 214 (accept_3_3 38 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 214 (Polychromatic418967fa.accept_18_1_7_16_1_1342 37 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 214 (Polychromatic418967fa.accept_27_9_7_25_1_2944 36 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 214 (accept_3_3 35 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 214 (Polychromatic418967fa.accept_16_2_9_6_1_4441 34 169
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 33 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 214 (accept_3_3 32 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 214 (Polychromatic418967fa.accept_19_11_17_5_1_8609 30 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 214 (accept_3_3 29 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 169
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 214 (accept_3_3 26 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 214 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 169 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 214 (accept_3_3 23 169 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 214 (Polychromatic418967fa.accept_18_4_7_16_1_2307 22 169 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 214 (accept_3_3 20 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 214 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 214 (accept_3_3 17 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 169
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 214 (accept_3_3 14 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 169 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 214 (accept_3_3 11 169 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 9 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 214 (accept_3_3 8 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 214 (Polychromatic418967fa.accept_17_6_16_10_1_2890 6 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 214 (accept_3_3 5 169 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 169 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 214 (accept_3_3 2 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 214 (Polychromatic418967fa.accept_18_1_7_16_1_1342 1 169 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 214)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 168 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 168 214 2 23 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 168 214 (Polychromatic418967fa.accept_20_5_8_14_1_5341 45 168 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 214 2 22 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 214
  (Polychromatic418967fa.accept_20_3_8_14_1_5342 43 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 168 214 2 21 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 168 214 (accept_3_3 41 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 214 2 20 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 168 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 168 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 214 2 19 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 214 2 18 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 168 214 (accept_3_3 35 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 168 214 2 17 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 168 214 (Polychromatic418967fa.accept_13_7_12_6_1_1039 33 168 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 168 214 2 16 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 214 2 15 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 214 (accept_3_3 29 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 214 2 14 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 168 214 (Polychromatic418967fa.accept_19_8_16_5_1_8583 27 168 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 168 214 2 13 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 168 214
  (Polychromatic418967fa.accept_17_8_15_10_1_10367 25 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 168 214 2 12 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 168 214 (accept_3_3 23 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 214 2 11 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 168 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 168 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 214 2 10 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 214 2 9 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 214 (accept_3_3 17 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 214 2 8 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 168 214 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 168 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 214 2 7 84 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 214 2 6 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 214 (accept_3_3 11 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 214 2 5 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 168 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 168 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 168 214 2 4 84 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 168 214
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 7 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 214 2 3 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 214 (accept_3_3 5 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168
  214 2 2 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  168 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 168 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 168 214 2 1 84 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 168 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 168 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 214)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 167 214 (Eq.refl Bool.true) (allA_of_3_1 48 167 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 49 166 214 (Eq.refl Bool.true) (allA_succ_of_gcd 48 166 214 2 24 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 166 214 (accept_3_3 47 166 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 166 214 2 23 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 166 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45
  166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 166 214 2 22 83 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 166 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 166 214 2 21 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 166 214 (accept_3_3 41 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 214 2 20 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 214 2 19 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 214 2 18 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 214 (accept_3_3 35 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 214 2 17 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 214 2 16 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 214
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 31 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 214 2 15 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 214 (accept_3_3 29 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 214 2 14 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 214 2 13 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 214 2 12 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 214 (accept_3_3 23 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 214 2 11 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 214 2 10 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 214 2 9 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 214 (accept_3_3 17 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 214 2 8 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 214 2 7 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 166 214 2 6 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 166 214 (accept_3_3 11 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 214 2 5 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 166 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 214 2 4 83 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 214
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 7 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 214 2 3 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 214 (accept_3_3 5 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  214 2 2 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 166 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 214 2 1 83 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 166 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 214)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 165 214 (Eq.refl Bool.true) (allA_succ_of_accept 49 165 214 (Polychromatic418967fa.accept_6_1_3_4_1_1
  49 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 214
  (Polychromatic418967fa.accept_19_10_13_5_1_3091 48 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 165 214 (accept_3_3 47 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 165 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 165 214 (Polychromatic418967fa.accept_19_7_13_5_1_7125 45 165
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 214 (accept_3_3 44 165
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 165 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 165 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 214 (accept_3_3 41 165 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 165 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 165 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 165 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 214 (accept_3_3 38
  165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 214
  (Polychromatic418967fa.accept_6_1_3_4_1_1 37 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 165 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 165 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 214 (accept_3_3 35 165 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 165 214 (Polychromatic418967fa.accept_21_13_18_4_1_11181 34 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 33 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 165 214 (accept_3_3 32 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 165 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 165 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 30 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 214 (accept_3_3 29 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 165 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 165 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 165 214 (accept_3_3 26 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 165 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 165 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 165 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 214 (accept_3_3 23 165 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 165 214
  (Polychromatic418967fa.accept_10_1_5_4_1_276 21 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 165 214 (accept_3_3 20 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 165 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 165 214 (Polychromatic418967fa.accept_12_6_9_10_1_565 18 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 214 (accept_3_3 17 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 165
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 165 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 165 214 (accept_3_3 14 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 165 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 165 214 (Polychromatic418967fa.accept_19_12_13_5_1_11331 12 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 214 (accept_3_3 11 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 165 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 165 214
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 214 (accept_3_3 8 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  165 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 165 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 214 (accept_3_3 5 165 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 165 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 165 214 (accept_3_3 2 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  165 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 165 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 165 214)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 164 214 (Eq.refl
  Bool.true) (allA_of_3_1 51 164 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 163 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 163 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 163 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 214 (accept_3_3 50 163 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 163 214 (Polychromatic418967fa.accept_7_6_2_4_1_291
  48 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 214 (accept_3_3 47
  163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 214
  (Polychromatic418967fa.accept_18_10_1_16_1_579 46 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 163 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 163 214 (accept_3_3 44 163 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 163 214 (Polychromatic418967fa.accept_13_4_7_6_1_2359 43 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 163 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 163 214 (accept_3_3 41 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 163 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 163 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 163 214 (accept_3_3 38 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 163 214
  (Polychromatic418967fa.accept_15_6_13_4_1_2040 36 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 163 214 (accept_3_3 35 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 163 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 163 214 (accept_3_3 32 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 163 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 163 214 (accept_3_3 29 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 214 (accept_3_3 26 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 214 (accept_3_3 23 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 214 (accept_3_3 20 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 214 (accept_3_3 17 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 214 (accept_3_3 14 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 214 (accept_3_3 11 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 214 (Polychromatic418967fa.accept_15_10_13_4_1_1210 10 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 214 (accept_3_3 8 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 214 (accept_3_3 5 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 163 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 214 (accept_3_3 2 163 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163
  214)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 162 214 (Eq.refl Bool.true) (allA_succ_of_gcd
  52 162 214 2 26 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 162 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 162 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 214 2 25 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 214 (Polychromatic418967fa.accept_16_1_2_6_1_2295
  49 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 214 2 24 81 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 214
  (accept_3_3 47 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 214 2 23 81 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 45 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 214 2 22 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 214 (Polychromatic418967fa.accept_16_11_2_6_1_1435 43 162 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 214 2 21 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 214 (accept_3_3 41 162 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 214 2 20 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 214
  (Polychromatic418967fa.accept_12_3_6_10_1_576 39 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 214 2 19 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 37 162 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 162 214 2 18 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 162 214 (accept_3_3 35 162 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 214 2 17 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33
  162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 162 214 2 16 81 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 162 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 214 2 15 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 214 (accept_3_3 29 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 162 214 2 14 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 162 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 162 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 162 214 2 13 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 214 2 12 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 214 (accept_3_3 23 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 162 214 2 11 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 162 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 21 162 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 162 214 2 10 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 214 2 9 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 214 (accept_3_3 17 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 162 214 2 8 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 162 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 15 162 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 214 2 7 81 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 214
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 214 2 6 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 214 (accept_3_3 11 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 214 2 5 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 162 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 9 162 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 214 2 4 81 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 162 214 2 3 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 162 214 (accept_3_3 5 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162
  214 2 2 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  162 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 162 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 162 214 2 1 81 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 162 214 (Polychromatic418967fa.accept_15_1_12_4_1_2022 1 162 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  214))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 161 214 (Eq.refl Bool.true) (allA_of_3_1 54
  161 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 160 214 (Eq.refl Bool.true) (allA_succ_of_gcd 54 160
  214 2 27 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  53 160 214 (accept_3_3 53 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 160 214 2 26 80 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 160 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 160 214 2 25 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 160 214 (Polychromatic418967fa.accept_12_1_4_10_1_209 49 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 160 214 2 24 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 160 214 (accept_3_3 47 160 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 160 214 2 23 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 160 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 160 214 2 22 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 160 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 43 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 160 214 2 21 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 160 214 (accept_3_3 41 160 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 160 214 2 20 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 160 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 39 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 160 214 2 19 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 160 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 160 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 160 214 2 18 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 160 214 (accept_3_3 35 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 160 214 2 17 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 160 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33
  160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 160 214 2 16 80 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 214 2 15 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 214 (accept_3_3 29 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 214 2 14 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 160 214 (Polychromatic418967fa.accept_21_6_13_4_1_6521 27 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 214 2 13 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 160 214 2 12 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 160 214 (accept_3_3 23 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 160 214 2 11 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 160 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 214 2 10 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 160 214 2 9 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 160 214 (accept_3_3 17 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 160 214 2 8 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 160 214 (Polychromatic418967fa.accept_13_2_4_6_1_2356 15 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 214 2 7 80 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 214 2 6 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 160 214 (accept_3_3 11 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 160 214 2 5 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 160 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 160 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 160 214 2 4 80 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 160 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 160 214 2 3 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 160 214 (accept_3_3 5 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160
  214 2 2 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  160 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 160 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 160 214 2 1 80 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 160 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 160 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 159 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 159 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 159 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 54 159
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 214 (accept_3_3 53 159
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 214
  (Polychromatic418967fa.accept_34_18_23_10_1_12647 52 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 214 (accept_3_3 50 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 159 214 (accept_3_3 47 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 159 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 214 (accept_3_3 44 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 159 214 (accept_3_3 41 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 159 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 40 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 159 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 214 (accept_3_3 38 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 159 214 (accept_3_3 35 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 159 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 214 (accept_3_3 32 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 159 214 (accept_3_3 29 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 159 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 159 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 214 (accept_3_3 26 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 214
  (Polychromatic418967fa.accept_18_6_15_16_1_7325 24 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 214 (accept_3_3 23 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 159 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 214 (accept_3_3 20 159 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19
  159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 159 214 (accept_3_3 17 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 159 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 159 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 214 (accept_3_3 14 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 12 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 159 214 (accept_3_3 11 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 159 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 10 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 214 (accept_3_3 8 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 159 214 (accept_3_3 5 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  159 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 159 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 159 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 214 (accept_3_3 2 159 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 158 214 (Eq.refl Bool.true) (allA_of_3_1 57
  158 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 157 214 (Eq.refl Bool.true) (allA_succ_of_accept 57
  157 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 157 214 (accept_3_3 56 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 157 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 157 214 (Polychromatic418967fa.accept_13_2_1_6_1_2365 54 157
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 214 (accept_3_3 53 157
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 52 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 157 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 157 214 (accept_3_3 50 157 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 157 214 (Polychromatic418967fa.accept_14_7_3_4_1_1816 49 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 157 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 157 214 (accept_3_3 47 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 157 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 157 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 157 214 (accept_3_3 44 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 157 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 157 214 (accept_3_3 41 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 157 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 157 214 (accept_3_3 38 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 157 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 37 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 157 214 (accept_3_3 35 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 157 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 157 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 214 (accept_3_3 32 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 30 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 214 (accept_3_3 29 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 214 (accept_3_3 26 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 214 (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 157 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 24 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 157 214 (accept_3_3 23 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 157 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 157 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 214 (accept_3_3 20 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 214
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 18 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 214 (accept_3_3 17 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 214 (accept_3_3 14 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 12 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 214 (accept_3_3 11 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 10 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 214 (accept_3_3 8 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 214 (accept_3_3 5 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 4 157 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 214 (accept_3_3 2 157 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 157 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 156 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 156 214 2 29 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 156 214 (Polychromatic418967fa.accept_21_15_9_4_1_2207 57 156 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 156 214 2 28 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 156 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 214 2 27 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 214 (accept_3_3 53 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 156 214 2 26 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 156 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 51 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 156 214 2 25 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 156 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 214 2 24 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 214 (accept_3_3 47 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 156 214 2 23 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 156 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 156 214 2 22 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 156 214
  (Polychromatic418967fa.accept_15_13_6_4_1_1221 43 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 214 2 21 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 214 (accept_3_3 41 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 156 214 2 20 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 156 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 39 156 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 156 214 2 19 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 156 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 37 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 214 2 18 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 214 (accept_3_3 35 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 156 214 2 17 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 156 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 214 2 16 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 214 2 15 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 214 (accept_3_3 29 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 214 2 14 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 156 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 214 2 13 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 214 2 12 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 214 (accept_3_3 23 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 156 214 2 11 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 156 214 (Polychromatic418967fa.accept_19_2_4_5_1_3021 21 156 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 214 2 10 78 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 214 2 9 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 214 (accept_3_3 17 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 214 2 8 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 156 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 15 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 214 2 7 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 214 2 6 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 214 (accept_3_3 11 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 214 2 5 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 214 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 156 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 214 2 4 78 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 214
  (Polychromatic418967fa.accept_17_7_3_10_1_2881 7 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 214 2 3 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 214 (accept_3_3 5 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156
  214 2 2 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  156 214 (Polychromatic418967fa.accept_22_3_2_16_1_12646 3 156 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 156 214 2 1 78 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 156 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 1 156 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 155 214 (Eq.refl Bool.true) (allA_of_3_1
  60 155 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 154 214 (Eq.refl Bool.true) (allA_succ_of_gcd 60
  154 214 2 30 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 154 214 (accept_3_3 59 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58
  154 214 2 29 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 154 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 57 154 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 214 2 28 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 214 (Polychromatic418967fa.accept_18_1_10_16_1_566
  55 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 154 214 2 27 77 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 154 214
  (accept_3_3 53 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 154 214 2 26 77 107 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 154 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 51 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 154 214 2 25 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 154 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 154 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 154 214 2 24 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 154 214 (accept_3_3 47 154 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 154 214 2 23 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 154 214
  (Polychromatic418967fa.accept_17_11_1_10_1_3925 45 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 154 214 2 22 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 154 214 (Polychromatic418967fa.accept_13_4_11_6_1_1033 43 154 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 154 214 2 21 77 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 154 214 (accept_3_3 41 154 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 154 214 2 20 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 154 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 39 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 154 214 2 19 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 154 214 (Polychromatic418967fa.accept_18_1_10_16_1_566 37 154 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 154 214 2 18 77 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 154 214 (accept_3_3 35 154 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 154 214 2 17 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 154 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 33 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 154 214 2 16 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 154 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 31 154 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 154 214 2 15 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 154 214 (accept_3_3 29 154 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 154 214 2 14 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 154 214 (Polychromatic418967fa.accept_19_8_2_5_1_5678
  27 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 214 2 13 77 107
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 214
  (Polychromatic418967fa.accept_31_25_30_28_1_12645 25 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 154 214 2 12 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 154 214 (accept_3_3 23 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 214 2 11 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 154 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 214 2 10 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 214
  (Polychromatic418967fa.accept_18_1_10_16_1_566 19 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 154 214 2 9 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 154 214 (accept_3_3 17 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 214 2 8 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 154 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 15 154 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 214 2 7 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 13 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 154 214 2 6 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 154 214 (accept_3_3 11 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 154 214 2 5 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 154 214 (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 154 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 214 2 4 77 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 214
  (Polychromatic418967fa.accept_17_7_1_10_1_2836 7 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 214 2 3 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 214 (accept_3_3 5 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  214 2 2 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 154 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 214 2 1 77 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 154 214 (Polychromatic418967fa.accept_18_1_10_16_1_566 1 154 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 153 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 153 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 214 (Polychromatic418967fa.accept_19_3_1_5_1_8549 60 153
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 214 (accept_3_3 59 153
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 58 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 153 214 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 153 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 214 (accept_3_3 56 153 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 214 (Polychromatic418967fa.accept_7_5_6_4_1_117
  54 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 214 (accept_3_3 53
  153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 52 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 214 (accept_3_3 50 153 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 153 214
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 153 214 (accept_3_3 47 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 153 214 (Polychromatic418967fa.accept_15_1_3_4_1_1217 46 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 153 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 214 (accept_3_3 44 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 153 214 (accept_3_3 41 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 153 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 214 (accept_3_3 38 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 214
  (Polychromatic418967fa.accept_21_15_6_4_1_4990 36 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 153 214 (accept_3_3 35 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 153 214 (Polychromatic418967fa.accept_16_2_9_6_1_4441 34 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 214 (accept_3_3 32 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 153 214 (accept_3_3 29 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 153 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 214 (accept_3_3 26 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 153 214 (accept_3_3 23 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 153 214 (Polychromatic418967fa.accept_13_9_10_6_1_1028 22 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 153 214 (Polychromatic418967fa.accept_20_1_13_14_1_1481 21 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 214 (accept_3_3 20 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 153 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 18 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 153 214 (accept_3_3 17 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 153 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 214 (accept_3_3 14 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 153 214 (accept_3_3 11 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 153 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 153 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 214 (accept_3_3 8 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 214
  (Polychromatic418967fa.accept_11_6_10_5_1_341 6 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 153 214 (accept_3_3 5 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  153 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 153 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 153 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 214 (accept_3_3 2 153 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 153 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 152 214 (Eq.refl Bool.true)
  (allA_of_3_1 63 152 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 151 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 151 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 151 214 (accept_3_3 62 151 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 151 214
  (Polychromatic418967fa.accept_25_10_1_14_1_10889 60 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 151 214 (accept_3_3 59 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 151 214 (Polychromatic418967fa.accept_11_3_8_5_1_336 58 151 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 151 214 (accept_3_3 56 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 151 214 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  55 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 151 214
  (Polychromatic418967fa.accept_13_2_8_6_1_2390 54 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 151 214 (accept_3_3 53 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 151 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 52 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 151 214 (accept_3_3 50 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 151 214
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 48 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 151 214 (accept_3_3 47 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 151 214 (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 151 214 (accept_3_3 44 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 214 (Polychromatic418967fa.accept_14_1_11_4_1_3430 43 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 151 214
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 42 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 151 214 (accept_3_3 41 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 151 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 40 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 214 (accept_3_3 38 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 151 214
  (Polychromatic418967fa.accept_11_3_8_5_1_336 36 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 151 214 (accept_3_3 35 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 151 214 (Polychromatic418967fa.accept_22_12_19_16_1_9551 34 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 214 (accept_3_3 32 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 214 (Polychromatic418967fa.accept_16_15_7_6_1_1453 31 151
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 151 214
  (Polychromatic418967fa.accept_20_10_11_14_1_8380 30 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 151 214 (accept_3_3 29 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 151 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 151 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 214 (accept_3_3 26 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25
  151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 151 214
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 24 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 151 214 (accept_3_3 23 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 214 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 214 (accept_3_3 20 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 214 (Polychromatic418967fa.accept_17_2_15_10_1_5171 19 151 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 214
  (Polychromatic418967fa.accept_15_3_1_4_1_1246 18 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 214 (accept_3_3 17 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 214 (accept_3_3 14 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 214
  (Polychromatic418967fa.accept_15_12_1_4_1_2899 12 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 214 (accept_3_3 11 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 214 (Polychromatic418967fa.accept_19_10_18_5_1_5673 10 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 214 (accept_3_3 8 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 214 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 214
  (Polychromatic418967fa.accept_19_6_18_5_1_5630 6 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 214 (accept_3_3 5 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 151 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 214 (accept_3_3 2 151 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 150 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 150 214 2 32 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 150 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 150 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 150 214 2 31 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 150 214
  (Polychromatic418967fa.accept_13_9_7_6_1_1673 61 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 214 2 30 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 214 (accept_3_3 59 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 150 214 2 29 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 150 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 150 214 2 28 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 150 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 214 2 27 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 214 (accept_3_3 53 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 150 214 2 26 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 150 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 51 150 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 214 2 25 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 214 2 24 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 214 (accept_3_3 47 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 150 214 2 23 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 150 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 45 150 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 150 214 2 22 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 150 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 214 2 21 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 214 (accept_3_3 41 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 214 2 20 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 150 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 150 214 2 19 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 37 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 214 2 18 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 214 (accept_3_3 35 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 214 2 17 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 150 214 (Polychromatic418967fa.accept_12_9_6_10_1_1085 33 150 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 150 214 2 16 75 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 31 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 214 2 15 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 214 (accept_3_3 29 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 214 2 14 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 150 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 150 214 2 13 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 150 214
  (Polychromatic418967fa.accept_13_12_7_6_1_1015 25 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 214 2 12 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 214 (accept_3_3 23 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 214 2 11 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 150 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 214 2 10 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 19 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 214 2 9 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 214 (accept_3_3 17 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 214 2 8 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 150 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 214 2 7 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 214 2 6 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 214 (accept_3_3 11 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 214 2 5 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 150 214 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 150 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 214 2 4 75 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 214
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 214 2 3 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 214 (accept_3_3 5 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150
  214 2 2 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  150 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 3 150 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 150 214 2 1 75 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 150 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 150 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 149 214 (Eq.refl Bool.true)
  (allA_of_3_1 66 149 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 148 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 148 214 2 33 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 148 214 (accept_3_3 65 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 148 214 2 32 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 148 214 (Polychromatic418967fa.accept_13_11_5_6_1_519 63 148 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 148 214 2 31 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 148 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 148 214 2 30 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 148 214 (accept_3_3 59 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 148 214 2 29 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 148 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 148 214 2 28 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 148 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 148 214 2 27 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 148 214 (accept_3_3 53 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 148 214 2 26 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 148 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 148 214 2 25 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 148 214
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 148 214 2 24 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 214 (accept_3_3 47 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 148 214 2 23 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 148 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 148 214 2 22 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 148 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 43 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 148 214 2 21 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 148 214 (accept_3_3 41 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 214 2 20 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 214 2 19 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 214 2 18 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 148 214 (accept_3_3 35 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 148 214 2 17 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 148 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 214 2 16 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 148 214 2 15 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 148 214 (accept_3_3 29 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 148 214 2 14 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 148 214 (Polychromatic418967fa.accept_13_1_5_6_1_1048 27 148 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 148 214 2 13 74 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 25 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 214 2 12 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 214 (accept_3_3 23 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 214 2 11 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 214 2 10 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 214 2 9 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 148 214 (accept_3_3 17 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 148 214 2 8 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 148 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 214 2 7 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 13 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 148 214 2 6 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 148 214 (accept_3_3 11 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 214 2 5 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 148 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 148 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 214 2 4 74 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 148 214 2 3 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 148 214 (accept_3_3 5 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148
  214 2 2 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  148 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 148 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 148 214 2 1 74 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 148 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 148 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 147 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 147 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 66 147
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 214 (accept_3_3 65 147
  214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 214 (Polychromatic418967fa.accept_9_1_3_7_1_6
  64 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 147 214
  (Polychromatic418967fa.accept_10_3_7_4_1_584 63 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 147 214 (accept_3_3 62 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 147 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 60 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 214 (accept_3_3 59 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 147 214 (accept_3_3 56 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 147 214 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 214 (accept_3_3 53 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 147
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 51 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 147 214 (accept_3_3 50 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 147 214 (Polychromatic418967fa.accept_13_9_4_6_1_1005 48 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 214 (accept_3_3 47 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 147 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 214 (accept_3_3 44 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 147 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 42 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 214 (accept_3_3 41 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 214
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 147 214 (accept_3_3 38 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 214 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 214 (accept_3_3 35 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 214 (Polychromatic418967fa.accept_16_2_3_6_1_3372 34 147
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 214 (accept_3_3 32 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 30 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 214 (accept_3_3 29 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 147 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 147 214
  (Polychromatic418967fa.accept_16_11_3_6_1_4462 27 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 214 (accept_3_3 26 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 24 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 214 (accept_3_3 23 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 22 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 147 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 147 214 (accept_3_3 20 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 147 214 (Polychromatic418967fa.accept_12_6_3_10_1_224 18 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 214 (accept_3_3 17 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 214 (Polychromatic418967fa.accept_15_1_12_4_1_2022 16 147
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 147 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 15 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 147 214 (accept_3_3 14 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 147 214 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 214 (accept_3_3 11 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 147 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 214
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 147 214 (accept_3_3 8 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  147 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 147 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 6 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 214 (accept_3_3 5 147 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 147 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 147 214
  (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 147 214 (accept_3_3 2 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  147 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 147 214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 146
  214 (Eq.refl Bool.true) (allA_of_3_1 69 146 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 145 214
  (Eq.refl Bool.true) (allA_succ_of_accept 69 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 145 214 (accept_3_3 68 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 145 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 145 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 66 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 145 214 (accept_3_3 65 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 145 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 145 214 (accept_3_3 62 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 145 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 61 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 145 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 145 214 (accept_3_3 59 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 145 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 145 214 (accept_3_3 56 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 145 214
  (Polychromatic418967fa.accept_15_9_10_4_1_2055 54 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 145 214 (accept_3_3 53 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 145 214 (Polychromatic418967fa.accept_11_8_2_5_1_1769 52 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 145 214 (accept_3_3 50 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 145 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 49 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 214 (accept_3_3 47 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 145 214 (accept_3_3 44 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 145 214 (accept_3_3 41 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 145 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 40 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 145 214 (accept_3_3 38 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 145 214 (accept_3_3 35 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 145 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 214 (accept_3_3 32 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 145 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 145 214 (accept_3_3 29 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 145 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 28 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 214 (accept_3_3 26 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 214 (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 145 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 24 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 145 214 (accept_3_3 23 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 145 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 21 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 214 (accept_3_3 20 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 214
  (Polychromatic418967fa.accept_16_2_1_6_1_2342 18 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 145 214 (accept_3_3 17 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 145 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 214 (accept_3_3 14 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 12 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 214 (accept_3_3 11 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 214 (Polychromatic418967fa.accept_13_10_2_6_1_1044 10 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 214 (accept_3_3 8 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 214 (accept_3_3 5 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 145 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 214 (accept_3_3 2 145 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 145 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 144 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 144 214 2 35 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 214 (Polychromatic418967fa.accept_19_12_11_5_1_950 69 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 214 2 34 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 214
  (Polychromatic418967fa.accept_13_2_1_6_1_2365 67 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 214 2 33 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 214 (accept_3_3 65 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 214 2 32 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 144 214 (Polychromatic418967fa.accept_17_12_8_10_1_6440 63 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 214 2 31 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 214
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 214 2 30 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 214 (accept_3_3 59 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 144 214 2 29 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 144 214 (Polychromatic418967fa.accept_13_5_1_6_1_2367 57 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 144 214 2 28 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 144 214
  (Polychromatic418967fa.accept_13_3_1_6_1_509 55 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 214 2 27 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 214 (accept_3_3 53 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 144 214 2 26 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 144 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 51 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 214 2 25 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 214
  (Polychromatic418967fa.accept_17_15_8_10_1_2886 49 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 144 214 2 24 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 144 214 (accept_3_3 47 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 214 2 23 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 214 (Polychromatic418967fa.accept_21_3_18_4_1_11234 45 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 214 2 22 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 214
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 43 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 214 2 21 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 214 (accept_3_3 41 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 144 214 2 20 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 144 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 144 214 2 19 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 214
  (Polychromatic418967fa.accept_25_12_19_14_1_12644 37 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 144 214 2 18 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 144 214 (accept_3_3 35 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 144 214 2 17 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 144 214 (Polychromatic418967fa.accept_13_7_1_6_1_3287 33 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 214 2 16 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 214
  (Polychromatic418967fa.accept_13_5_1_6_1_2367 31 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 214 2 15 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 214 (accept_3_3 29 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 214 2 14 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 144 214 (Polychromatic418967fa.accept_15_12_9_4_1_3898 27 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 214 2 13 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 214
  (Polychromatic418967fa.accept_15_10_9_4_1_2924 25 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 214 2 12 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 214 (accept_3_3 23 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 214 2 11 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 214 (Polychromatic418967fa.accept_13_8_1_6_1_997 21 144 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 214 2 10 72 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 214
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 19 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 214 2 9 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 214 (accept_3_3 17 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 214 2 8 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 144 214 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 214 2 7 72 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 214
  (Polychromatic418967fa.accept_15_13_9_4_1_3892 13 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 214 2 6 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 214 (accept_3_3 11 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 214 2 5 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 144 214 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 144 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 214 2 4 72 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 214
  (Polychromatic418967fa.accept_13_7_1_6_1_3287 7 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 214 2 3 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 214 (accept_3_3 5 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144
  214 2 2 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  144 214 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 144 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 144 214 2 1 72 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 144 214 (Polychromatic418967fa.accept_21_1_18_4_1_4975 1 144 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 143 214 (Eq.refl Bool.true)
  (allA_of_3_1 72 143 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 142 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 142 214 2 36 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 142 214 (accept_3_3 71 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 142 214 2 35 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 142 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 69 142 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 142 214 2 34 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 142 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 67 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 142 214 2 33 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 142 214 (accept_3_3 65 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 142 214 2 32 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 142 214 (Polychromatic418967fa.accept_15_3_7_4_1_1225 63 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 142 214 2 31 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 142 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 61 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 142 214 2 30 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 142 214 (accept_3_3 59 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 142 214 2 29 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 142 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 142 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 142 214 2 28 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 142 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 142 214 2 27 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 142 214 (accept_3_3 53 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 142 214 2 26 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 142 214 (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 142 214 2 25 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 142 214
  (Polychromatic418967fa.accept_13_10_12_6_1_991 49 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 142 214 2 24 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 142 214 (accept_3_3 47 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 142 214 2 23 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 142 214 (Polychromatic418967fa.accept_19_7_9_5_1_8590 45 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 214 2 22 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 214
  (Polychromatic418967fa.accept_23_20_4_7_1_12643 43 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 142 214 2 21 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 142 214 (accept_3_3 41 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 214 2 20 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 214 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 214 2 19 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 214 2 18 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 214 (accept_3_3 35 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 214 2 17 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 142 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 214 2 16 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 214
  (Polychromatic418967fa.accept_13_5_12_6_1_508 31 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 214 2 15 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 214 (accept_3_3 29 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 214 2 14 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 142 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 214 2 13 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 214
  (Polychromatic418967fa.accept_15_10_7_4_1_1222 25 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 214 2 12 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 214 (accept_3_3 23 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 214 2 11 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 214 (Polychromatic418967fa.accept_17_4_6_10_1_5164 21 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 214 2 10 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 214 2 9 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 142 214 (accept_3_3 17 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 142 214 2 8 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 142 214 (Polychromatic418967fa.accept_11_4_10_5_1_1202 15 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 142 214 2 7 71 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 142 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 142 214 2 6 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 142 214 (accept_3_3 11 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 142 214 2 5 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 142 214 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 142 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 142 214 2 4 71 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 142 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 142 214 2 3 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 142 214 (accept_3_3 5 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 142
  214 2 2 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  142 214 (Polychromatic418967fa.accept_15_3_7_4_1_1225 3 142 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 142 214 2 1 71 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 142 214 (Polychromatic418967fa.accept_19_1_9_5_1_9939 1 142 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 141 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 214
  (Polychromatic418967fa.accept_21_9_15_4_1_2190 72 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 214 (accept_3_3 71 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 141 214 (Polychromatic418967fa.accept_13_5_11_6_1_505 70 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 214 (Polychromatic418967fa.accept_13_4_11_6_1_1033 69 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 214 (accept_3_3 68 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 141 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 214 (accept_3_3 65 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 141 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 64 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 214 (accept_3_3 62 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 214
  (Polychromatic418967fa.accept_13_8_11_6_1_1035 60 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 141 214 (accept_3_3 59 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 141 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 58 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 141 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 214 (accept_3_3 56 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 141 214 (accept_3_3 53 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 141 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 214 (accept_3_3 50 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 48 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 141 214 (accept_3_3 47 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 141 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 46 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 141 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 214 (accept_3_3 44 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 42 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 141 214 (accept_3_3 41 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 141 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 214 (accept_3_3 38 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 214
  (Polychromatic418967fa.accept_16_4_13_6_1_4417 36 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 141 214 (accept_3_3 35 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 141 214 (Polychromatic418967fa.accept_13_8_11_6_1_1035 34 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 141 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 214 (accept_3_3 32 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 214
  (Polychromatic418967fa.accept_9_3_6_7_1_562 30 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 141 214 (accept_3_3 29 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 141 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 28 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 214 (accept_3_3 26 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 141 214 (accept_3_3 23 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 141 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 22 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 141 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 214 (accept_3_3 20 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 141 214 (accept_3_3 17 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 141 214 (Polychromatic418967fa.accept_19_16_8_5_1_4322 16 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 214 (accept_3_3 14 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 141 214 (accept_3_3 11 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 141 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 141 214 (Polychromatic418967fa.accept_15_9_6_4_1_1220 9 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 214 (accept_3_3 8 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 6 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 141 214 (accept_3_3 5 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  141 214 (Polychromatic418967fa.accept_9_4_6_7_1_286 4 141 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 141 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 214 (accept_3_3 2 141 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 141 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 140 214 (Eq.refl
  Bool.true) (allA_of_3_1 75 140 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 139 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 139 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 139 214 (accept_3_3 74 139 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 139 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 72
  139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 214 (accept_3_3 71
  139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 214
  (Polychromatic418967fa.accept_21_7_13_4_1_2169 70 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 139 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 139 214 (accept_3_3 68 139 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 139 214 (Polychromatic418967fa.accept_13_2_9_6_1_501 67 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 139 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 66 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 139 214 (accept_3_3 65 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 139 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 64 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 139 214 (accept_3_3 62 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 139 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 60 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 139 214 (accept_3_3 59 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 139 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 139 214 (accept_3_3 56 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 139 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 55 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 139 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 139 214 (accept_3_3 53 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 139 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 214 (accept_3_3 50 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 214
  (Polychromatic418967fa.accept_9_3_4_7_1_89 48 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 139 214 (accept_3_3 47 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 139 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 46 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 139 214 (accept_3_3 44 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 139 214 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 139 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 42 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 139 214 (accept_3_3 41 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 139 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 139 214 (accept_3_3 38 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 214
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 36 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 139 214 (accept_3_3 35 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 139 214 (Polychromatic418967fa.accept_16_2_11_6_1_737 34 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 214 (accept_3_3 32 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 139 214 (accept_3_3 29 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 139 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 28 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 214 (accept_3_3 26 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 139 214 (accept_3_3 23 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 139 214 (Polychromatic418967fa.accept_19_3_6_5_1_9947 22 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 139 214 (accept_3_3 20 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 139 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 139 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 139 214 (accept_3_3 17 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 139 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 139 214 (accept_3_3 14 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 139 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 139 214 (accept_3_3 11 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 139 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 139 214 (accept_3_3 8 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 139 214 (Polychromatic418967fa.accept_13_7_9_6_1_148 7 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 139 214
  (Polychromatic418967fa.accept_9_6_4_7_1_300 6 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 139 214 (accept_3_3 5 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  139 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 4 139 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 139 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 139 214 (accept_3_3 2 139 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 139 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 139
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 138 214 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 138 214 2 38 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 138 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 75 138 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 138 214 2 37 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 138 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 73 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 214 2 36 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 214 (accept_3_3 71 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 138 214 2 35 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 138 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 69 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 138 214 2 34 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 138 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 67 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 214 2 33 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 214 (accept_3_3 65 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 138 214 2 32 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 138 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 63 138 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 138 214 2 31 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 138 214
  (Polychromatic418967fa.accept_15_1_3_4_1_1217 61 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 214 2 30 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 214 (accept_3_3 59 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 138 214 2 29 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 138 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 138 214 2 28 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 138 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 55 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 214 2 27 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 214 (accept_3_3 53 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 138 214 2 26 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 138 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 138 214 2 25 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 49 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 214 2 24 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 214 (accept_3_3 47 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 138 214 2 23 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 138 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 138 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 138 214 2 22 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 214
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 214 2 21 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 214 (accept_3_3 41 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 138 214 2 20 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 138 214 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 138 214 2 19 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 214
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 214 2 18 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 214 (accept_3_3 35 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 138 214 2 17 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 138 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 138 214 2 16 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 214
  (Polychromatic418967fa.accept_9_4_3_7_1_296 31 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 214 2 15 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 214 (accept_3_3 29 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 138 214 2 14 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 138 214 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 138 214 2 13 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 214
  (Polychromatic418967fa.accept_17_8_2_10_1_2879 25 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 214 2 12 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 214 (accept_3_3 23 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 138 214 2 11 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 138 214 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 138 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 138 214 2 10 69 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 214
  (Polychromatic418967fa.accept_9_1_3_7_1_6 19 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 214 2 9 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 214 (accept_3_3 17 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 138 214 2 8 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 138 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 214 2 7 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 214
  (Polychromatic418967fa.accept_7_6_5_4_1_297 13 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 214 2 6 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 214 (accept_3_3 11 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 214 2 5 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 138 214 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 138 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 214 2 4 69 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 214
  (Polychromatic418967fa.accept_15_7_3_4_1_574 7 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 214 2 3 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 214 (accept_3_3 5 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138
  214 2 2 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  138 214 (Polychromatic418967fa.accept_12_3_6_10_1_576 3 138 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 138 214 2 1 69 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 138 214 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 138 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 137 214 (Eq.refl
  Bool.true) (allA_of_3_1 78 137 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 136 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 78 136 214 2 39 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 136 214 (accept_3_3 77 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 136 214 2 38 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 136 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 75 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 136 214 2 37 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 136 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 73 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 136 214 2 36 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 136 214 (accept_3_3 71 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 136 214 2 35 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 136 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 136 214 2 34 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 136 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 67 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 136 214 2 33 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 136 214 (accept_3_3 65 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 136 214 2 32 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 136 214 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 136 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 136 214 2 31 68 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 136 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 61 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 136 214 2 30 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 136 214 (accept_3_3 59 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 136 214 2 29 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 136 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 136 214 2 28 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 136 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 55 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 136 214 2 27 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 136 214 (accept_3_3 53 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 136 214 2 26 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 136 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 51 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 214 2 25 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 49 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 214 2 24 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 214 (accept_3_3 47 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 136 214 2 23 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 136 214 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 214 2 22 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 43 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 214 2 21 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 214 (accept_3_3 41 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 214 2 20 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 136 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 39 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 214 2 19 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 214
  (Polychromatic418967fa.accept_12_1_4_10_1_209 37 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 136 214 2 18 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 136 214 (accept_3_3 35 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 136 214 2 17 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 136 214 (Polychromatic418967fa.accept_9_6_1_7_1_577 33 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 136 214 2 16 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 136 214
  (Polychromatic418967fa.accept_9_4_1_7_1_293 31 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 136 214 2 15 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 136 214 (accept_3_3 29 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 136 214 2 14 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 136 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 214 2 13 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 214
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 214 2 12 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 214 (accept_3_3 23 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 214 2 11 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 21 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 214 2 10 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 19 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 136 214 2 9 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 136 214 (accept_3_3 17 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 214 2 8 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 136 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 214 2 7 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 136 214 2 6 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 136 214 (accept_3_3 11 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 136 214 2 5 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 136 214 (Polychromatic418967fa.accept_22_9_4_16_1_4545 9 136 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 214 2 4 68 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 214
  (Polychromatic418967fa.accept_12_7_4_10_1_572 7 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 214 2 3 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 214 (accept_3_3 5 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  214 2 2 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 214 (Polychromatic418967fa.accept_9_3_1_7_1_97 3 136 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 214 2 1 68 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 136 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 135 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 79 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 214 (Polychromatic418967fa.accept_12_6_3_10_1_224
  78 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 214 (accept_3_3 77
  135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 76 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 135 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 75 135 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 214 (accept_3_3 74 135 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735
  72 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 214 (accept_3_3 71
  135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 214
  (Polychromatic418967fa.accept_20_10_15_14_1_6797 70 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 214 (accept_3_3 68 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 67 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 66 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 135 214 (accept_3_3 65 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 135 214 (Polychromatic418967fa.accept_13_12_5_6_1_1050 64 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 135 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 214 (accept_3_3 62 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 135 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 214
  (Polychromatic418967fa.accept_17_9_16_10_1_362 60 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 135 214 (accept_3_3 59 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 135 214 (Polychromatic418967fa.accept_14_2_9_4_1_1735 58 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 214 (accept_3_3 56 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 55 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 54 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 214 (accept_3_3 53 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 135 214 (Polychromatic418967fa.accept_11_8_3_5_1_355 52 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 214 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 214 (accept_3_3 50 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 135 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 48 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 135 214 (accept_3_3 47 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 135 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 214 (accept_3_3 44 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 43 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 42 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 214 (accept_3_3 41 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 135 214 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 135 214 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 214 (accept_3_3 38 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 214
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 135 214 (accept_3_3 35 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 135 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 214 (accept_3_3 32 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 31 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 214
  (Polychromatic418967fa.accept_11_8_3_5_1_355 30 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 135 214 (accept_3_3 29 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 135 214 (Polychromatic418967fa.accept_20_8_15_14_1_1487 28 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 135 214 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 214 (accept_3_3 26 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 214
  (Polychromatic418967fa.accept_13_11_5_6_1_519 24 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 214 (accept_3_3 23 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 135 214 (Polychromatic418967fa.accept_19_3_2_5_1_5679 22 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 214 (accept_3_3 20 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 19 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 214
  (Polychromatic418967fa.accept_12_6_3_10_1_224 18 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 135 214 (accept_3_3 17 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 135 214 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 135 214 (Polychromatic418967fa.accept_16_15_7_6_1_1453 15 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 214 (accept_3_3 14 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 214
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 135 214 (accept_3_3 11 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 135 214 (Polychromatic418967fa.accept_13_10_5_6_1_1671 10 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 214 (accept_3_3 8 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 7 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 214
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 135 214 (accept_3_3 5 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  135 214 (Polychromatic418967fa.accept_13_4_5_6_1_3201 4 135 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 135 214 (Polychromatic418967fa.accept_13_3_5_6_1_3192 3 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 214 (accept_3_3 2 135 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 134 214 (Eq.refl
  Bool.true) (allA_of_3_1 81 134 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 82 133 214 (Eq.refl Bool.true)
  (allA_succ_of_accept 81 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 81 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 133 214 (accept_3_3 80 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 133 214
  (Polychromatic418967fa.accept_22_12_1_16_1_3122 78 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 133 214 (accept_3_3 77 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 133 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 76 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 214 (accept_3_3 74 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 133 214 (Polychromatic418967fa.accept_14_3_7_4_1_118
  73 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 214
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 72 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 214 (accept_3_3 71 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 133 214 (Polychromatic418967fa.accept_13_5_3_6_1_3278 70 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 69 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 214 (accept_3_3 68 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 214
  (Polychromatic418967fa.accept_13_1_3_6_1_158 66 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 133 214 (accept_3_3 65 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 133 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 64 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 133 214 (accept_3_3 62 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 133 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 214
  (Polychromatic418967fa.accept_21_18_7_4_1_8131 60 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 133 214 (accept_3_3 59 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 214 (Polychromatic418967fa.accept_17_7_14_10_1_1846 58 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 57 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 214 (accept_3_3 56 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 214
  (Polychromatic418967fa.accept_15_9_13_4_1_1209 54 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 214 (accept_3_3 53 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 52 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 214 (accept_3_3 50 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 214 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 214
  (Polychromatic418967fa.accept_13_9_3_6_1_1661 48 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 214 (accept_3_3 47 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 214 (Polychromatic418967fa.accept_25_21_8_14_1_12642 46 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 45 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 214 (accept_3_3 44 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 214
  (Polychromatic418967fa.accept_25_17_8_14_1_12641 42 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 133 214 (accept_3_3 41 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 133 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 40 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 214 (accept_3_3 38 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 214 (Polychromatic418967fa.accept_10_7_3_4_1_978
  37 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 214
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 36 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 214 (accept_3_3 35 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 214 (Polychromatic418967fa.accept_21_13_7_4_1_4991 34 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 33 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 214 (accept_3_3 32 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 214
  (Polychromatic418967fa.accept_17_13_14_10_1_1847 30 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 133 214 (accept_3_3 29 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 133 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388 28 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 214 (accept_3_3 26 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 214
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 214 (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 214 (accept_3_3 23 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 214 (Polychromatic418967fa.accept_13_9_3_6_1_1661 22 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 214
  (Polychromatic418967fa.accept_6_3_1_4_1_25 21 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 214 (accept_3_3 20 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 214 (Polychromatic418967fa.accept_13_5_3_6_1_3278 18 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 214 (accept_3_3 17 133 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 214 (Polychromatic418967fa.accept_12_4_1_10_1_221 16 133
  214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 214
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 214 (accept_3_3 14 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 214 (Polychromatic418967fa.accept_17_13_14_10_1_1847 13 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 214 (Polychromatic418967fa.accept_21_12_7_4_1_12629 12 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 214 (accept_3_3 11 133 214
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 214
  (Polychromatic418967fa.accept_13_10_3_6_1_1003 10 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 133 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 9 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 214 (accept_3_3 8 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 214 (Polychromatic418967fa.accept_11_6_1_5_1_2388
  6 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 214 (accept_3_3 5
  133 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 214
  (Polychromatic418967fa.accept_12_4_1_10_1_221 4 133 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 133 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 214 (accept_3_3 2 133 214 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 133 214 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 133 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 132 214 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 132 214 2 41 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 132 214 (Polychromatic418967fa.accept_21_18_6_4_1_5031 81 132 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 132 214 2 40 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 132 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 79 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 214 2 39 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 214 (accept_3_3 77 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 132 214 2 38 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 132 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 75 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 132 214 2 37 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 132 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 73 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 214 2 36 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 214 (accept_3_3 71 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 132 214 2 35 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 132 214 (Polychromatic418967fa.accept_13_4_2_6_1_1043 69 132 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 132 214 2 34 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 132 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 67 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 214 2 33 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 214 (accept_3_3 65 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 132 214 2 32 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 132 214 (Polychromatic418967fa.accept_19_6_18_5_1_5630 63 132 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 132 214 2 31 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 132 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 61 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 214 2 30 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 214 (accept_3_3 59 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 132 214 2 29 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 132 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 57 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 132 214 2 28 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 214
  (Polychromatic418967fa.accept_9_1_6_7_1_285 55 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 214 2 27 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 214 (accept_3_3 53 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 132 214 2 26 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 132 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 132 214 2 25 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 49 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 214 2 24 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 214 (accept_3_3 47 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 132 214 2 23 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 132 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 132 214 2 22 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 214
  (Polychromatic418967fa.accept_13_4_2_6_1_1043 43 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 214 2 21 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 214 (accept_3_3 41 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 132 214 2 20 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 132 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 39 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 132 214 2 19 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 214
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 214 2 18 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 214 (accept_3_3 35 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 132 214 2 17 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 132 214 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 214 2 16 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 214
  (Polychromatic418967fa.accept_7_3_6_4_1_30 31 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 214 2 15 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 214 (accept_3_3 29 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 214 2 14 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 132 214 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 214 2 13 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 214
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 25 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 214 2 12 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 214 (accept_3_3 23 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 132 214 2 11 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 132 214 (Polychromatic418967fa.accept_9_3_6_7_1_562 21 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 214 2 10 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 214
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 214 2 9 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 214 (accept_3_3 17 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 214 2 8 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 132 214 (Polychromatic418967fa.accept_18_15_6_16_1_4730 15 132 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 214 2 7 66 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 214
  (Polychromatic418967fa.accept_9_4_6_7_1_286 13 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 214 2 6 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 214 (accept_3_3 11 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 214 2 5 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 132 214 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 132 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 214 2 4 66 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 214
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 214 2 3 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 214 (accept_3_3 5 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132
  214 2 2 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  132 214 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 132 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 132 214 2 1 66 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 132 214 (Polychromatic418967fa.accept_9_1_6_7_1_285 1 132 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 131 214 (Eq.refl
  Bool.true) (allA_of_3_1 84 131 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 85 130 214 (Eq.refl Bool.true)
  (allA_succ_of_gcd 84 130 214 2 42 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 130 214 (accept_3_3 83 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 130 214 2 41 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 130 214 (Polychromatic418967fa.accept_15_6_10_4_1_150 81 130 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 130 214 2 40 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 130 214
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 79 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 130 214 2 39 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 130 214 (accept_3_3 77 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 130 214 2 38 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 130 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 75 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 130 214 2 37 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 130 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 73 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 130 214 2 36 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 130 214 (accept_3_3 71 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 130 214 2 35 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 130 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 69 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 130 214 2 34 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 130 214
  (Polychromatic418967fa.accept_15_7_10_4_1_151 67 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 130 214 2 33 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 130 214 (accept_3_3 65 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 130 214 2 32 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 130 214 (Polychromatic418967fa.accept_23_17_15_7_1_11085 63 130 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 130 214 2 31 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 214
  (Polychromatic418967fa.accept_18_7_4_16_1_2299 61 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 130 214 2 30 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 130 214 (accept_3_3 59 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 130 214 2 29 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 130 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 57 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 130 214 2 28 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 130 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 55 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 130 214 2 27 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 130 214 (accept_3_3 53 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 130 214 2 26 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 130 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 51 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 214 2 25 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 214
  (Polychromatic418967fa.accept_16_1_2_6_1_2295 49 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 214 2 24 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 214 (accept_3_3 47 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 214 2 23 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 214 (Polychromatic418967fa.accept_20_5_10_14_1_5317 45 130 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 214 2 22 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 214
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 43 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 130 214 2 21 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 130 214 (accept_3_3 41 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 214 2 20 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 39 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 214 2 19 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 37 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 214 2 18 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 214 (accept_3_3 35 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 214 2 17 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 33 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 214 2 16 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 214
  (Polychromatic418967fa.accept_19_12_16_5_1_12620 31 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 214 2 15 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 214 (accept_3_3 29 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 214 2 14 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 214 (Polychromatic418967fa.accept_16_11_2_6_1_1435 27 130 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 214 2 13 65 107 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 214
  (Polychromatic418967fa.accept_16_9_2_6_1_4434 25 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 214 2 12 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 214 (accept_3_3 23 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 214 2 11 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 21 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 214 2 10 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 214
  (Polychromatic418967fa.accept_9_1_4_7_1_7 19 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 214 2 9 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 130 214 (accept_3_3 17 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 130 214 2 8 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 130 214 (Polychromatic418967fa.accept_9_6_4_7_1_300 15 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 130 214 2 7 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 130 214
  (Polychromatic418967fa.accept_15_13_10_4_1_1232 13 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 130 214 2 6 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 130 214 (accept_3_3 11 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 130 214 2 5 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 130 214 (Polychromatic418967fa.accept_15_9_10_4_1_2055 9 130 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 214 2 4 65 107 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 214
  (Polychromatic418967fa.accept_11_7_9_5_1_338 7 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 214 2 3 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 214 (accept_3_3 5 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  214 2 2 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 214 (Polychromatic418967fa.accept_9_3_4_7_1_89 3 130 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 214 2 1 65 107 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 130 214 (Polychromatic418967fa.accept_9_1_4_7_1_7 1 130 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 129 214
  (Eq.refl Bool.true) (allA_succ_of_accept 85 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 85 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 214
  (Polychromatic418967fa.accept_20_4_9_14_1_5316 84 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 129 214 (accept_3_3 83 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 129 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 82 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 129 214 (Polychromatic418967fa.accept_15_6_9_4_1_1227 81 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 214 (accept_3_3 80 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 79 129 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 78 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 129 214 (accept_3_3 77 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 129 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 76 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 214 (accept_3_3 74 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 73 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 214
  (Polychromatic418967fa.accept_13_7_12_6_1_1039 72 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 129 214 (accept_3_3 71 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 129 214 (Polychromatic418967fa.accept_13_5_12_6_1_508 70 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 129 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 69 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 214 (accept_3_3 68 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 67 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 66 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 129 214 (accept_3_3 65 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 129 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 214 (accept_3_3 62 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 61 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 60 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 129 214 (accept_3_3 59 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 129 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 58 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 129 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 57 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 214 (accept_3_3 56 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 54 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 129 214 (accept_3_3 53 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 129 214 (Polychromatic418967fa.accept_22_8_19_16_1_6137 52 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 214 (accept_3_3 50 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 49 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 48 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 129 214 (accept_3_3 47 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 129 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 46 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 129 214 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 214 (accept_3_3 44 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 42 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 129 214 (accept_3_3 41 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 129 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 40 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 214 (accept_3_3 38 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 37 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 214
  (Polychromatic418967fa.accept_7_1_3_4_1_128 36 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 129 214 (accept_3_3 35 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 129 214 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 129 214 (Polychromatic418967fa.accept_9_6_3_7_1_580 33 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 214 (accept_3_3 32 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 214
  (Polychromatic418967fa.accept_12_6_9_10_1_565 30 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 129 214 (accept_3_3 29 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 129 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 28 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 214 (accept_3_3 26 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 25 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 214
  (Polychromatic418967fa.accept_9_6_3_7_1_580 24 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 129 214 (accept_3_3 23 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 129 214 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 129 214 (Polychromatic418967fa.accept_14_7_3_4_1_1816 21 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 214 (accept_3_3 20 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 214
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 129 214 (accept_3_3 17 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 129 214 (Polychromatic418967fa.accept_23_16_14_7_1_12640 16 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 214 (accept_3_3 14 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 13 129 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 214
  (Polychromatic418967fa.accept_15_12_9_4_1_3898 12 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 129 214 (accept_3_3 11 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 129 214 (Polychromatic418967fa.accept_9_1_3_7_1_6 10 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 129 214 (Polychromatic418967fa.accept_19_9_15_5_1_5666 9 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 214 (accept_3_3 8 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 214
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 129 214 (accept_3_3 5 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  129 214 (Polychromatic418967fa.accept_9_4_3_7_1_296 4 129 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 129 214 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 214 (accept_3_3 2 129 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 214 (Polychromatic418967fa.accept_6_1_3_4_1_1 1 129 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  214)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 128 214
  (Eq.refl Bool.true) (allA_of_3_1 87 128 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 127 214 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 87 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 214 (accept_3_3 86 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 85 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 84 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 214 (accept_3_3 83 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 82 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 214 (accept_3_3 80 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 214 (Polychromatic418967fa.accept_18_7_1_16_1_578 79 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 78 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 214 (accept_3_3 77 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 76 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 75 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 214 (accept_3_3 74 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 73 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 214
  (Polychromatic418967fa.accept_10_2_7_4_1_967 72 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 214 (accept_3_3 71 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 214 (Polychromatic418967fa.accept_13_5_10_6_1_2361 70 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 214 (accept_3_3 68 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 67 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 66 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 214 (accept_3_3 65 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 64 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 63 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 214 (accept_3_3 62 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 61 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 60 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 214 (accept_3_3 59 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 58 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 214 (accept_3_3 56 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 214 (Polychromatic418967fa.accept_13_3_10_6_1_2382 55 127 214
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 214 (accept_3_3 53 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 51 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 214 (accept_3_3 50 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 48 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 214 (accept_3_3 47 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 214 (Polychromatic418967fa.accept_17_12_8_10_1_6440 46 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 214 (accept_3_3 44 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 214 (Polychromatic418967fa.accept_10_3_7_4_1_584 43 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 42 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 214 (accept_3_3 41 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 39 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 214 (accept_3_3 38 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 214
  (Polychromatic418967fa.accept_17_2_8_10_1_2870 36 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 214 (accept_3_3 35 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 214 (Polychromatic418967fa.accept_11_1_6_5_1_1732 34 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 214 (accept_3_3 32 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 214
  (Polychromatic418967fa.accept_9_3_1_7_1_97 30 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 214 (accept_3_3 29 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 28 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 27 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 214 (accept_3_3 26 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 214
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 214 (accept_3_3 23 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 22 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 214 (accept_3_3 20 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 214 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 214
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 18 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 214 (accept_3_3 17 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 214 (Polychromatic418967fa.accept_12_4_7_10_1_563 16 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 15 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 214 (accept_3_3 14 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 214
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 214 (accept_3_3 11 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 214 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 214 (accept_3_3 8 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 214 (Polychromatic418967fa.accept_16_7_15_6_1_1428 7 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 214
  (Polychromatic418967fa.accept_9_6_1_7_1_577 6 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 214 (accept_3_3 5 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 214 (Polychromatic418967fa.accept_9_4_1_7_1_293 4 127 214 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 214 (Polychromatic418967fa.accept_6_3_1_4_1_25 3 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 214 (accept_3_3 2 127 214 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 214 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 214 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  214))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_214_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


