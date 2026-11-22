-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch204
-- name    : Polychromatic418967fa_Branch204
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:13.879632+00:00
-- url     : https://prove2.me/theorems/933c26b2-aff5-4da0-a7dc-6494fd7e2f8b
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch204_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_204 : allB 204 204 :=
  allB_succ' 2 203 204 (Eq.refl Bool.true) (allA_succ_of_accept 1 203 204 (accept_3_4 1 203 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 203 204)) (allB_succ' 3 202 204 (Eq.refl Bool.true) (allA_succ_of_gcd 2 202 204 2 1 101
  102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 204
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 202 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 204))) (allB_succ' 4 201 204 (Eq.refl Bool.true) (allA_succ_of_gcd 3 201 204 3 1 67 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 201 204
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 201 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 204 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 201 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 201 204)))) (allB_succ' 5 200 204 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  200 204 4 1 50 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 200 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 200 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 200 204 2 1 100 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 200 204 (accept_3_4 1 200 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 200 204))))) (allB_succ' 6 199 204 (Eq.refl Bool.true) (allA_succ_of_accept 5 199 204 (accept_3_5 5 199 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 199 204 (Polychromatic418967fa.accept_7_4_3_1_1_87 4
  199 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 199 204
  (Polychromatic418967fa.accept_8_3_7_4_1_42 3 199 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 199 204 (accept_3_5 2 199 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  199 204 (Polychromatic418967fa.accept_19_1_9_14_1_526 1 199 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 199 204)))))) (allB_succ' 7 198 204 (Eq.refl Bool.true) (allA_succ_of_gcd 6 198 204 6 1 33 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 204
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 5 198 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 204 2 2 99 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 198 204 3 1 66 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 198 204 2 1 99 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 198 204 (Polychromatic418967fa.accept_14_1_2_8_1_655 1 198 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 204))))))) (allB_succ' 8 197 204 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 197 204 (accept_3_4 7 197 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  197 204 (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 197 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 197 204 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 197 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 204 (accept_3_4 4 197 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 204 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 197 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 204
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 197 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 197 204 (accept_3_4 1 197 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197
  204)))))))) (allB_succ' 9 196 204 (Eq.refl Bool.true) (allA_succ_of_gcd 8 196 204 4 2 49 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 196 204
  (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 196 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 196 204 2 3 98 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 196 204 (accept_3_5 5 196 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196
  204 4 1 49 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  196 204 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 196 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 196 204 2 1 98 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 196 204 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 196 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 204))))))))) (allB_succ' 10 195 204 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 195 204 3 3 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 195 204 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 195 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 204 (Polychromatic418967fa.accept_8_7_3_4_1_404 7
  195 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 204 3 2 65 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 195 204
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 195 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 195 204 (Polychromatic418967fa.accept_16_4_3_12_1_4892 4 195 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 204 3 1 65 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 204 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 195 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 204
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 195 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 195 204)))))))))) (allB_succ' 11 194 204 (Eq.refl Bool.true) (allA_succ_of_gcd 10 194 204 2 5 97 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 204
  (Polychromatic418967fa.accept_16_9_2_12_1_1800 9 194 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 204 2 4 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 204 (accept_3_4 7 194 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  204 2 3 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 204 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 194 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 204 2 2 97 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 204 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 194 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 204 2 1 97 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 204 (accept_3_4 1 194 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 204))))))))))) (allB_succ' 12 193 204 (Eq.refl Bool.true)
  (allA_succ_of_accept 11 193 204 (accept_3_5 11 193 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 193 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 193 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 193 204 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 193 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 193 204 (accept_3_5 8 193 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 204 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 193 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 204
  (Polychromatic418967fa.accept_21_6_4_15_1_9005 6 193 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 204 (accept_3_5 5 193 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 204 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 193 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 193 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 204 (accept_3_5 2 193 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 204 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 193 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 204)))))))))))) (allB_succ' 13 192 204 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 192 204 12 1 16 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 192 204 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 204 2 5 96 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 204 3 3 64 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 204 4 2 48 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 192 204
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 192 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 192 204 6 1 32 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 192 204 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 192 204 4 1 48 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 204 3 1 64 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 192 204 2 1 96 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 204 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 192 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 204))))))))))))) (allB_succ' 14 191 204
  (Eq.refl Bool.true) (allA_succ_of_accept 13 191 204 (accept_3_4 13 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 191 204 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 191 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 191 204 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 191 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 204 (accept_3_4 10 191 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 204 (Polychromatic418967fa.accept_19_9_1_14_1_1372
  9 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 204
  (Polychromatic418967fa.accept_9_8_2_6_1_875 8 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 204 (accept_3_4 7 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 204 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 204 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 191 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 204 (accept_3_4 4 191 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 204 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 191 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 204
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 204 (accept_3_4 1 191 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  204)))))))))))))) (allB_succ' 15 190 204 (Eq.refl Bool.true) (allA_succ_of_gcd 14 190 204 2 7 95 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 190 204
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 190 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 190 204 2 6 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 190 204 (accept_3_5 11 190 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 190 204 2 5 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 190 204 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 190 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 190 204 2 4 95 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 190 204
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 190 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 190 204 2 3 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 190 204 (accept_3_5 5 190 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 190
  204 2 2 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  190 204 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 190 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 190 204 2 1 95 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 190 204 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 190 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 204))))))))))))))) (allB_succ' 16 189 204 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 189 204 3 5 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 189 204 (Polychromatic418967fa.accept_18_14_9_6_1_1777 14 189 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 204
  (Polychromatic418967fa.accept_10_3_9_4_1_960 13 189 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 204 3 4 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 204 (Polychromatic418967fa.accept_13_11_7_9_1_612 11 189 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 204 (Polychromatic418967fa.accept_16_10_13_12_1_4873 10
  189 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 204 3 3 63 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 204
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 189 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 204 (Polychromatic418967fa.accept_18_7_9_6_1_4023 7 189 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 204 3 2 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 204 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 189 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 204
  (Polychromatic418967fa.accept_11_4_2_6_1_389 4 189 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 204 3 1 63 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 204 (Polychromatic418967fa.accept_13_2_7_9_1_2616 2 189 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 204 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 189 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 204)))))))))))))))) (allB_succ' 17 188 204
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 188 204 4 4 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 188 204 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 188 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 188 204 2 7 94 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 188 204 (accept_3_4 13 188 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 188 204 4 3 47 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 188 204
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 188 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 188 204 2 5 94 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 188 204 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 188 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 188 204 4 2 47 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 188 204 (accept_3_4 7 188 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188 204 2 3 94 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 188 204 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 188 204 4 1 47 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 188 204
  (Polychromatic418967fa.accept_9_3_8_6_1_80 3 188 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 188 204 2 1 94 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 188 204 (accept_3_4 1 188 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  204))))))))))))))))) (allB_succ' 18 187 204 (Eq.refl Bool.true) (allA_succ_of_gcd 17 187 204 17 1 11 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 187 204
  (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 187 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 187 204 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 204 (accept_3_5 14 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 187 204 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 187 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 204 (Polychromatic418967fa.accept_9_3_7_6_1_76 12
  187 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 204 (accept_3_5 11
  187 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 204
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 187 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 187 204 (Polychromatic418967fa.accept_18_9_7_6_1_5331 9 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 204 (accept_3_5 8 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 187 204 (Polychromatic418967fa.accept_8_7_3_4_1_404 7 187 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 204 (Polychromatic418967fa.accept_7_6_5_1_1_416 6
  187 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 204 (accept_3_5 5 187
  204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 204
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 187 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 187 204 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 204 (accept_3_5 2 187 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 187 204 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 187 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 204)))))))))))))))))) (allB_succ' 19 186 204 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 186 204 6 3 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 186 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 204 2 8 93 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 204 3 5 62 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 204 2 7 93 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 204
  (Polychromatic418967fa.accept_16_13_10_12_1_1811 13 186 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 186 204 6 2 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 186 204 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 186 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 204 2 5 93 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 204 3 3 62 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 204 2 4 93 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 204
  (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 186 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 204 6 1 31 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 204 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 186 204 2 2 93 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 186 204 3 1 62 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 204 2 1 93 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 204 (Polychromatic418967fa.accept_15_1_6_9_1_254 1
  186 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 204))))))))))))))))))) (allB_succ'
  20 185 204 (Eq.refl Bool.true) (allA_succ_of_accept 19 185 204 (accept_3_4 19 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 185 204 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 185 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 204 (Polychromatic418967fa.accept_9_8_5_6_1_538
  17 185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 204 (accept_3_4 16
  185 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 204
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 185 204 (Polychromatic418967fa.accept_11_3_9_6_1_105 14 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 204 (accept_3_4 13 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 185 204 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 204 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 204 (accept_3_4 10
  185 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 204
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 204 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 204 (accept_3_4 7 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 204 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 185 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 204 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 204 (accept_3_4 4 185
  204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 204
  (Polychromatic418967fa.accept_9_3_5_6_1_253 3 185 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 204 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 204 (accept_3_4 1 185 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185 204)))))))))))))))))))) (allB_succ' 21 184 204 (Eq.refl Bool.true) (allA_succ_of_gcd 20 184
  204 4 5 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  184 204 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 184 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 184 204 2 9 92 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 184 204 (accept_3_5 17 184 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 184 204 4 4 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 184 204 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 184 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 204 2 7 92 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 204 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  184 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 184 204 4 3 46 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 184 204 (accept_3_5 11
  184 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 184 204 2 5 92 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 184 204
  (Polychromatic418967fa.accept_16_9_8_12_1_979 9 184 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 184 204 4 2 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 184 204 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 184 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 184 204 2 3 92 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 184 204 (accept_3_5 5 184 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184 204 4 1 46 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 184 204 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 184 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 184 204 2 1 92 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 184 204
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 184 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 184 204))))))))))))))))))))) (allB_succ' 22 183 204 (Eq.refl Bool.true) (allA_succ_of_gcd 21 183 204 3 7 61
  68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 204
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 204 (Polychromatic418967fa.accept_8_3_7_4_1_42 19 183 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 204 3 6 61 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 204 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 204
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 204 3 5 61 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 204 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 183 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 204 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 183 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 204 3 4 61 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 204
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 204 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 183 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 204 3 3 61 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 204 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 204
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 204 3 2 61 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 204 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 183 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 204 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 183 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 204 3 1 61 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 204
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 183 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 204 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 204)))))))))))))))))))))) (allB_succ' 23 182 204 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 182 204 2 11 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 182 204 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 182 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 182 204 2 10 91 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 182 204 (accept_3_4 19 182 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 182 204 2 9 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 182 204 (Polychromatic418967fa.accept_9_8_2_6_1_875 17
  182 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 204 2 8 91 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 204
  (Polychromatic418967fa.accept_19_15_11_14_1_11940 15 182 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 204 2 7 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 204 (accept_3_4 13 182 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 204 2 6 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 204 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 182 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 204 2 5 91 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 204
  (Polychromatic418967fa.accept_18_9_2_6_1_9322 9 182 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 204 2 4 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 204 (accept_3_4 7 182 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  204 2 3 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 204 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 182 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 204 2 2 91 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 204 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 204 2 1 91 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 204 (accept_3_4 1 182 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 204))))))))))))))))))))))) (allB_succ' 24 181 204 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 181 204 (accept_3_5 23 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 181 204 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 181 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 204 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 181 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 204 (accept_3_5 20 181 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 204 (Polychromatic418967fa.accept_7_5_6_1_1_407
  19 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 204
  (Polychromatic418967fa.accept_19_18_10_14_1_2392 18 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 181 204 (accept_3_5 17 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 181 204 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 181 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 204 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 181
  204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 204 (accept_3_5 14 181
  204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 204
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 181 204 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 181 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 204 (accept_3_5 11 181 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 181 204 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 181 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 204
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 204 (accept_3_5 8 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 204 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 204 (Polychromatic418967fa.accept_15_6_1_9_1_1476 6 181 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 204 (accept_3_5 5 181 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 204 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 181 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 204
  (Polychromatic418967fa.accept_9_3_1_6_1_86 3 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 204 (accept_3_5 2 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 204 (Polychromatic418967fa.accept_8_1_5_4_1_388 1 181 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 204)))))))))))))))))))))))) (allB_succ' 25 180 204 (Eq.refl Bool.true) (allA_succ_of_gcd 24
  180 204 12 2 15 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 204 (Polychromatic418967fa.accept_16_7_4_12_1_1806 23 180 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 204 2 11 90 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 204 3 7 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 204 4 5 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 204 (Polychromatic418967fa.accept_16_3_4_12_1_3799
  19 180 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 204 6 3 30 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 204
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 180 204 4 4 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 180 204 3 5 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 180 204 2 7 90 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 204 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 180 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 204 12 1 15 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 204
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 204 2 5 90 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 180 204 3 3 60 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 180 204 4 2 45 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 180 204 (Polychromatic418967fa.accept_13_7_11_9_1_1858 7 180 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 204 6 1 30 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 204 (Polychromatic418967fa.accept_16_5_4_12_1_3800
  5 180 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 204 4 1 45 51 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 204 3 1 60 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 204 2 1 90 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 204
  (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 180 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 204))))))))))))))))))))))))) (allB_succ' 26 179 204 (Eq.refl Bool.true) (allA_succ_of_accept 25 179 204
  (accept_3_4 25 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 204
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 179 204 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 204 (accept_3_4 22 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 179 204 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 179 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 204 (Polychromatic418967fa.accept_9_2_8_6_1_79 20
  179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 204 (accept_3_4 19
  179 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 204
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 179 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 204 (accept_3_4 16 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 179 204 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 179 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 204 (Polychromatic418967fa.accept_9_5_8_6_1_281
  14 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 204 (accept_3_4 13
  179 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 204
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 179 204 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 204 (accept_3_4 10 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 179 204 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 179 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 204 (Polychromatic418967fa.accept_10_8_9_4_1_961 8
  179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 204 (accept_3_4 7 179
  204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 204
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 6 179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 179 204 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 204 (accept_3_4 4 179 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 179 204 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 179 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 204 (Polychromatic418967fa.accept_9_2_8_6_1_79 2
  179 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 204 (accept_3_4 1 179
  204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179 204)))))))))))))))))))))))))) (allB_succ' 27 178 204
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 178 204 2 13 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 204 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 178 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 178 204 2 12 89 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 178 204 (accept_3_5 23
  178 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 178 204 2 11 89 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 178 204
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 178 204 2 10 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 178 204 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 178 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 178 204 2 9 89 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 178 204 (accept_3_5 17 178 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 178 204 2 8 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 178 204 (Polychromatic418967fa.accept_11_4_2_6_1_389
  15 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 204 2 7 89 102
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 204
  (Polychromatic418967fa.accept_9_4_7_6_1_255 13 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 204 2 6 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 204 (accept_3_5 11 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 204 2 5 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 204 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 178 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 204 2 4 89 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 204
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 204 2 3 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 204 (accept_3_5 5 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  204 2 2 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 204 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 204 2 1 89 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 204 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 178 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 204))))))))))))))))))))))))))) (allB_succ' 28 177
  204 (Eq.refl Bool.true) (allA_succ_of_gcd 27 177 204 3 9 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 204 (Polychromatic418967fa.accept_19_7_6_14_1_11872 26 177
  204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 204
  (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 177 204 3 8 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 177 204 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 204 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 177
  204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 177 204 3 7 59 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 177 204
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 204 (Polychromatic418967fa.accept_15_4_12_9_1_773 19 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 204 3 6 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 204 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 204
  (Polychromatic418967fa.accept_11_5_1_6_1_774 16 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 177 204 3 5 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 177 204 (Polychromatic418967fa.accept_13_1_8_9_1_1154 14 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 204 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 177 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 204 3 4 59 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 204
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 204 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 204 3 3 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 204 (Polychromatic418967fa.accept_16_8_1_12_1_984 8 177 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 204
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 177 204 3 2 59 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 204 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 204 (Polychromatic418967fa.accept_13_4_8_9_1_1156 4 177 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 204 3 1 59 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 204
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 177 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 204 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 177 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 204)))))))))))))))))))))))))))) (allB_succ' 29 176 204 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 176 204 4 7 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 176 204 (Polychromatic418967fa.accept_18_9_14_6_1_1790 27 176 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 204 2 13 88 102 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 204 (accept_3_4 25 176 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 204 4 6 44 51 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 204
  (Polychromatic418967fa.accept_21_2_8_15_1_11906 23 176 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 176 204 2 11 88 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 176 204 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 176 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 204 4 5 44 51 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 204 (accept_3_4 19 176 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 204 2 9 88 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 204
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 176 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 176 204 4 4 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 176 204 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 176 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 176 204 2 7 88 102 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 176 204 (accept_3_4 13 176 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 176 204 4 3 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 176 204 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 176 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 204 2 5 88 102 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 204
  (Polychromatic418967fa.accept_18_9_14_6_1_1790 9 176 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 204 4 2 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 204 (accept_3_4 7 176 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  204 2 3 88 102 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 204 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 176 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 204 4 1 44 51 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 176 204 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 176 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 204 2 1 88 102 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 204 (accept_3_4 1 176 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 176 204))))))))))))))))))))))))))))) (allB_succ' 30 175 204 (Eq.refl
  Bool.true) (allA_succ_of_accept 29 175 204 (accept_3_5 29 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 175 204 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 175 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 175 204 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 175 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 204 (accept_3_5 26 175 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 175 204 (Polychromatic418967fa.accept_9_7_4_6_1_273
  25 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 204
  (Polychromatic418967fa.accept_16_8_15_12_1_1747 24 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 175 204 (accept_3_5 23 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 175 204 (Polychromatic418967fa.accept_20_2_15_4_1_7575 22 175 204 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 204 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 175 204
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 175 204 (accept_3_5 20 175 204
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 204 (Polychromatic418967fa.accept_8_3_7_4_1_42 19
  175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 175 204
  (Polychromatic418967fa.accept_15_3_10_9_1_769 18 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 175 204 (accept_3_5 17 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 175 204 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 175 204 (Polychromatic418967fa.accept_13_2_6_9_1_2636 15 175 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 175 204 (accept_3_5 14 175 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 204 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 175
  204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 204
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 204 (accept_3_5 11 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 175 204 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 175 204 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 175 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 204 (accept_3_5 8 175 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 204 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 204
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 204 (accept_3_5 5 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 204 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 175 204 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 204 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 175 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 204 (accept_3_5 2 175 204 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 204 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 204 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 204))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_204_segment_001)))))))))))))))))))))))))))))


