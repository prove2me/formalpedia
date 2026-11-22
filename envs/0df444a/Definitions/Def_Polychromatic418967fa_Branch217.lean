-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch217
-- name    : Polychromatic418967fa_Branch217
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:24:31.927498+00:00
-- url     : https://prove2.me/theorems/f6b9bcbf-85ae-4084-a619-3e5c8d575a6a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch217_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_217 : allB 217 217 :=
  allB_succ' 2 216 217 (Eq.refl Bool.true) (allA_succ_of_accept 1 216 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1
  216 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 216 217)) (allB_succ' 3 215 217
  (Eq.refl Bool.true) (allA_of_3_1 3 215 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 4 214 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 3 214 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 214 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 214 217 (accept_3_3 2 214 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 214 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 214 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 214 217)))) (allB_succ' 5 213 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 4 213 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 213 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 213 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 213 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 213 217 (accept_3_3 2 213 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918
  1 213 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 217))))) (allB_succ' 6 212 217
  (Eq.refl Bool.true) (allA_of_3_1 6 212 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 7 211 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 6 211 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 211 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 211 217 (accept_3_3 5 211 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 211 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 4 211 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 211 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 211 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 211 217 (accept_3_3 2 211 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  211 217 (Polychromatic418967fa.accept_19_1_2_8_1_10129 1 211 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 211 217))))))) (allB_succ' 8 210 217 (Eq.refl Bool.true) (allA_succ_of_gcd 7 210 217 7 1 30 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 210 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 210 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 210 217 (accept_3_3 5 210 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  210 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 210 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 210 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 210 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 210 217 (accept_3_3 2 210 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 210 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 210 217)))))))) (allB_succ' 9 209 217 (Eq.refl
  Bool.true) (allA_of_3_1 9 209 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 10 208 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 208 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 208 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 208 217 (accept_3_3 8 208 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 208 217 (Polychromatic418967fa.accept_19_7_18_8_1_1067 7 208 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 208 217
  (Polychromatic418967fa.accept_15_6_13_7_1_222 6 208 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 208 217 (accept_3_3 5 208 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  208 217 (Polychromatic418967fa.accept_19_4_18_8_1_10117 4 208 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 208 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 208 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 208 217 (accept_3_3 2 208 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 208 217 (Polychromatic418967fa.accept_19_1_18_8_1_1066 1 208 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 208 217)))))))))) (allB_succ' 11 207 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 10 207 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 207 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 207 217 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  207 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 207 217 (accept_3_3 8 207
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 217
  (Polychromatic418967fa.accept_28_7_11_21_1_12928 7 207 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 207 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 217 (accept_3_3 5 207 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 207 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 217
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 3 207 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 217 (accept_3_3 2 207 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  207 217 (Polychromatic418967fa.accept_26_1_25_9_1_12927 1 207 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 217))))))))))) (allB_succ' 12 206 217 (Eq.refl Bool.true) (allA_of_3_1 12 206 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 13 205 217 (Eq.refl Bool.true) (allA_succ_of_accept 12 205 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 205 217 (accept_3_3 11 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 205 217 (Polychromatic418967fa.accept_20_10_5_17_1_8556 10 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 205 217 (Polychromatic418967fa.accept_21_9_16_7_1_5222 9 205 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 205 217 (accept_3_3 8 205 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 205 217 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 205
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 205 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 205 217 (accept_3_3 5 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  205 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 205 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 205 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 3 205 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 217 (accept_3_3 2 205 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 205 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 205 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 217))))))))))))) (allB_succ' 14 204 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 13 204 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 204 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 204 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 12
  204 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 204 217 (accept_3_3 11
  204 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 204 217
  (Polychromatic418967fa.accept_21_10_15_7_1_3784 10 204 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 204 217 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 204 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 204 217 (accept_3_3 8 204 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 204 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 217
  (Polychromatic418967fa.accept_14_6_8_7_1_589 6 204 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 204 217 (accept_3_3 5 204 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  204 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 204 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 204 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 204 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 204 217 (accept_3_3 2 204 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 204 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 204 217)))))))))))))) (allB_succ' 15 203 217 (Eq.refl
  Bool.true) (allA_of_3_1 15 203 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 16 202 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 202 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 202 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 202 217 (accept_3_3 14 202 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 202 217 (Polychromatic418967fa.accept_14_13_6_7_1_2013 13 202 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 202 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 202 217 (accept_3_3 11 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 202 217 (Polychromatic418967fa.accept_19_10_12_8_1_10124 10 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 202 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 202 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 202 217 (accept_3_3 8 202 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 202 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 202 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 202 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 202 217 (accept_3_3 5 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  202 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 202 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 202 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 202 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 202 217 (accept_3_3 2 202 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 202 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 202 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 202 217)))))))))))))))) (allB_succ' 17 201 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 16 201 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 201 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 201 217 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 217 (accept_3_3 14
  201 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 217
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 201 217 (Polychromatic418967fa.accept_14_12_5_7_1_2010 12 201 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 201 217 (accept_3_3 11 201 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 201 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 201 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 217 (Polychromatic418967fa.accept_14_9_5_7_1_1251
  9 201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 217 (accept_3_3 8
  201 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 217
  (Polychromatic418967fa.accept_9_7_3_1_1_386 7 201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 201 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 201 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 201 217 (accept_3_3 5 201 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 201 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 201 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 217 (Polychromatic418967fa.accept_12_3_9_1_1_290 3
  201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 217 (accept_3_3 2 201
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 217
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 201 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 201 217))))))))))))))))) (allB_succ' 18 200 217 (Eq.refl Bool.true) (allA_of_3_1 18 200 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 19 199 217 (Eq.refl Bool.true) (allA_succ_of_accept 18 199 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 199 217 (accept_3_3 17 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 199 217 (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 199 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 199 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 199 217 (accept_3_3 14 199 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 199 217 (Polychromatic418967fa.accept_16_13_7_9_1_2606 13 199
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 199 217
  (Polychromatic418967fa.accept_10_2_9_7_1_720 12 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 199 217 (accept_3_3 11 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 199 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 217 (Polychromatic418967fa.accept_21_9_10_7_1_383 9 199 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 217 (accept_3_3 8 199 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 217 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 199 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 217 (accept_3_3 5 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 199 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 217 (Polychromatic418967fa.accept_15_3_4_7_1_1352 3 199 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 217 (accept_3_3 2 199 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 217 (Polychromatic418967fa.accept_17_1_12_13_1_448 1 199 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 217))))))))))))))))))) (allB_succ' 20 198 217
  (Eq.refl Bool.true) (allA_succ_of_accept 19 198 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 198 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 198 217
  (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 198 217 (accept_3_3 17 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 198 217 (Polychromatic418967fa.accept_21_16_9_7_1_6709 16 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 198 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 198 217 (accept_3_3 14 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 217 (Polychromatic418967fa.accept_16_13_6_9_1_2561 13 198 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 217
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 198 217 (accept_3_3 11 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 198 217 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 198 217 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 198 217 (accept_3_3 8 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 198 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 217
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 198 217 (accept_3_3 5 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  198 217 (Polychromatic418967fa.accept_15_4_3_7_1_713 4 198 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 198 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 198 217 (accept_3_3 2 198 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 217 (Polychromatic418967fa.accept_20_1_18_17_1_712 1 198 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 217)))))))))))))))))))) (allB_succ' 21 197 217
  (Eq.refl Bool.true) (allA_of_3_1 21 197 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 22 196 217 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 196 217 7 3 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 196 217 (accept_3_3 20 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 196 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 196 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 196 217 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 196
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 196 217 (accept_3_3 17 196
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 196 217
  (Polychromatic418967fa.accept_17_16_9_13_1_3087 16 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 196 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 196 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 196 217 7 2 28 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 196 217
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 196 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 196 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 196 217 (accept_3_3 11 196 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 196 217 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 196 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 196 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 196 217 (accept_3_3 8 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 196
  217 7 1 28 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  196 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 196 217 (accept_3_3 5 196 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 196 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 196 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 196 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 196 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 217 (accept_3_3 2 196 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 196 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1
  196 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 217))))))))))))))))))))))
  (allB_succ' 23 195 217 (Eq.refl Bool.true) (allA_succ_of_accept 22 195 217 (Polychromatic418967fa.accept_4_2_3_1_1_2
  22 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 195 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 195 217 (accept_3_3 20 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 195 217 (Polychromatic418967fa.accept_20_19_15_17_1_7059 19 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 195 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 195 217 (accept_3_3 17 195 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 195 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 217
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 195 217 (accept_3_3 14 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 195 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 195 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 195 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 217 (accept_3_3 11 195 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 195 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 195 217 (accept_3_3 8 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  195 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 195 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 195 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 195 217 (accept_3_3 5 195 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 195 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 217 (accept_3_3 2 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  195 217 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 195 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 217))))))))))))))))))))))) (allB_succ' 24 194 217 (Eq.refl Bool.true) (allA_of_3_1 24 194
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 25 193 217 (Eq.refl Bool.true) (allA_succ_of_accept 24 193
  217 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 193 217 (accept_3_3 23 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 193 217 (Polychromatic418967fa.accept_21_1_4_7_1_3689 22 193 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 193 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 21 193 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 193 217 (accept_3_3 20 193 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 193 217
  (Polychromatic418967fa.accept_17_2_6_13_1_2056 19 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 193 217 (Polychromatic418967fa.accept_14_4_11_7_1_1234 18 193 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 193 217 (accept_3_3 17 193 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 193 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 193 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 217 (Polychromatic418967fa.accept_9_6_4_1_1_390
  15 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 193 217 (accept_3_3 14
  193 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 193 217
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 13 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 193 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 193 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 217 (accept_3_3 11 193 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 193 217 (Polychromatic418967fa.accept_14_10_11_7_1_1955 10 193 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 217
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 217 (accept_3_3 8 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 193 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 217 (accept_3_3 5 193 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 193 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 217 (accept_3_3 2 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 217 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 193 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 217))))))))))))))))))))))))) (allB_succ' 26 192 217 (Eq.refl Bool.true) (allA_succ_of_accept
  25 192 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 192 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 192 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 192 217 (accept_3_3 23 192 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 192 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 192 217
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 192 217 (accept_3_3 20 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 192 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 192 217 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 217 (accept_3_3 17 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 192 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 192 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 192 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 192 217 (accept_3_3 14 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 192 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 192 217 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 217 (accept_3_3 11 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 192 217 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 192
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 192 217
  (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 192 217 (accept_3_3 8 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  192 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 192 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 192 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 217 (accept_3_3 5 192 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 192 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 192 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 192 217
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 192 217 (accept_3_3 2 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  192 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 192 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 192 217)))))))))))))))))))))))))) (allB_succ' 27 191 217 (Eq.refl Bool.true) (allA_of_3_1 27 191
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 28 190 217 (Eq.refl Bool.true) (allA_succ_of_accept 27 190
  217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 190 217 (accept_3_3 26 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 190 217 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 190 217 (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 190 217 (accept_3_3 23 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 190 217 (Polychromatic418967fa.accept_26_22_8_9_1_12926 22 190
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 190 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 190 217 (accept_3_3 20 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 190 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 190 217 (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 190 217 (accept_3_3 17 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 190 217 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 190
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 190 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 190 217 (accept_3_3 14 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 190 217 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 190 217 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 190 217 (accept_3_3 11 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 190 217 (Polychromatic418967fa.accept_17_10_3_13_1_6639 10 190
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 190 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 190 217 (accept_3_3 8 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  190 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 190 217 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 190 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 217 (accept_3_3 5 190 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 190 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 190 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 190 217 (accept_3_3 2 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  190 217 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 190 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 217)))))))))))))))))))))))))))) (allB_succ' 29 189 217 (Eq.refl Bool.true) (allA_succ_of_gcd
  28 189 217 7 4 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 189 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 189 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 189 217 (accept_3_3 26 189 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 189 217 (Polychromatic418967fa.accept_29_25_15_14_1_12925 25 189 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 217
  (Polychromatic418967fa.accept_13_11_7_9_1_612 24 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 189 217 (accept_3_3 23 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 189 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 21 189 217 7 3 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 20 189 217 (accept_3_3 20 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 217 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 189 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 189
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 217 (accept_3_3 17 189
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 217
  (Polychromatic418967fa.accept_6_4_3_1_1_57 16 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 189 217 (Polychromatic418967fa.accept_12_3_9_1_1_290 15 189 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 189 217 7 2 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 189 217 (Polychromatic418967fa.accept_15_13_9_7_1_2194
  13 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 189 217 (accept_3_3 11 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 189 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 189 217 (Polychromatic418967fa.accept_19_9_18_8_1_8782 9 189 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 217 (accept_3_3 8 189 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 189 217 7 1 27 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 189 217 (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 189 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 217 (accept_3_3 5 189 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4
  189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 189 217 (accept_3_3 2 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  189 217 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 189 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 189 217))))))))))))))))))))))))))))) (allB_succ' 30 188 217 (Eq.refl Bool.true) (allA_of_3_1 30
  188 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 31 187 217 (Eq.refl Bool.true) (allA_succ_of_accept 30
  187 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 187 217 (accept_3_3 29 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 187 217 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 187 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 187 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 27 187
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 187 217 (accept_3_3 26 187
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 187 217
  (Polychromatic418967fa.accept_19_6_16_8_1_10116 25 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 187 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 187 217 (accept_3_3 23 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 187 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 187 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 187 217 (accept_3_3 20 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 187 217 (Polychromatic418967fa.accept_20_19_7_17_1_7030 19 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 187 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 187 217 (accept_3_3 17 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 187 217 (Polychromatic418967fa.accept_13_3_5_9_1_5285 16 187 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 187 217 (accept_3_3 14 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 187 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 187 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 187 217 (accept_3_3 11 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 187 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 187 217
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 187 217 (accept_3_3 8 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  187 217 (Polychromatic418967fa.accept_19_7_16_8_1_8761 7 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 187 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 187 217 (accept_3_3 5 187 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 187 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 217 (accept_3_3 2 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 187 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 217))))))))))))))))))))))))))))))) (allB_succ' 32 186 217 (Eq.refl Bool.true)
  (allA_succ_of_gcd 31 186 217 31 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 30 186 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 186 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 186 217 (accept_3_3 29 186 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 186 217 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 186 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 186 217 (accept_3_3 26 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 186 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 186 217 (Polychromatic418967fa.accept_14_10_4_7_1_1214 24 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 186 217 (accept_3_3 23 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 186 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 186 217 (accept_3_3 20 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 186 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 186 217 (Polychromatic418967fa.accept_13_5_4_9_1_601 18 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 186 217 (accept_3_3 17 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 186 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 186 217 (accept_3_3 14 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 186 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 186 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 186 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 186 217 (accept_3_3 11 186 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 217 (Polychromatic418967fa.accept_14_10_4_7_1_1214 10 186 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 217
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 186 217 (accept_3_3 8 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  186 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 186 217 (Polychromatic418967fa.accept_13_6_4_9_1_4326 6 186 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 186 217 (accept_3_3 5 186 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 186 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 186 217 (accept_3_3 2 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  186 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 186 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 186 217)))))))))))))))))))))))))))))))) (allB_succ' 33 185 217 (Eq.refl Bool.true) (allA_of_3_1
  33 185 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 34 184 217 (Eq.refl Bool.true) (allA_succ_of_accept 33
  184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 184 217 (accept_3_3 32 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 184 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 184 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 184 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 184 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 184 217 (accept_3_3 29 184 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 184 217
  (Polychromatic418967fa.accept_16_12_8_9_1_2583 28 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 184 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 184 217 (accept_3_3 26 184 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 184 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 184 217 (Polychromatic418967fa.accept_9_6_4_1_1_390
  24 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 184 217 (accept_3_3 23
  184 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 184 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 184 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 184 217 (accept_3_3 20 184 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 184 217 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 184 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 184 217
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 184 217 (accept_3_3 17 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 217 (accept_3_3 14 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 184 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 217 (accept_3_3 11 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 217 (accept_3_3 8 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 184 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 217 (accept_3_3 5 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 217 (Polychromatic418967fa.accept_16_4_8_9_1_4639 4 184 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 217 (accept_3_3 2 184 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 184 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 217)))))))))))))))))))))))))))))))))) (allB_succ' 35
  183 217 (Eq.refl Bool.true) (allA_succ_of_accept 34 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 183 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 217 (accept_3_3 32 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 183 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 217 (accept_3_3 29 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 217
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 217 (accept_3_3 26 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 183 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 217 (accept_3_3 23 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 217 (accept_3_3 20 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 183 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 217 (accept_3_3 17 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 183 217 (accept_3_3 14 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 183 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 183 217 (Polychromatic418967fa.accept_15_12_3_7_1_4123 12 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 217 (accept_3_3 11 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 183 217 (accept_3_3 8 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  183 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 183 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 217 (accept_3_3 5 183 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 183 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 217
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 3 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 183 217 (accept_3_3 2 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  183 217 (Polychromatic418967fa.accept_19_1_12_8_1_8799 1 183 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 183 217))))))))))))))))))))))))))))))))))) (allB_succ' 36 182 217 (Eq.refl Bool.true)
  (allA_of_3_1 36 182 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 37 181 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 181 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 181 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 181 217 (accept_3_3 35 181 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 181 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 34 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 181 217
  (Polychromatic418967fa.accept_16_1_5_9_1_1649 33 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 181 217 (accept_3_3 32 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 181 217 (Polychromatic418967fa.accept_19_12_10_8_1_3270 31 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 181 217 (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 181 217 (accept_3_3 29 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 181 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 181 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 217
  (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 181 217 (accept_3_3 26 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 181 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 181 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 181 217 (accept_3_3 23 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 181 217 (Polychromatic418967fa.accept_14_8_13_7_1_2798 22 181
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 181 217
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 181 217 (accept_3_3 20 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 181 217 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 181 217 (Polychromatic418967fa.accept_19_18_10_8_1_2088 18 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 217 (accept_3_3 17 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 181 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 181
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 217
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 15 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 181 217 (accept_3_3 14 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 181 217 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 181 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 181 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 217 (accept_3_3 11 181 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 217 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 181 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 217
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 181 217 (accept_3_3 8 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  181 217 (Polychromatic418967fa.accept_17_7_11_13_1_2037 7 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 181 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 181 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 217 (accept_3_3 5 181 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 181 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 181 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 217
  (Polychromatic418967fa.accept_11_3_5_8_1_458 3 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 181 217 (accept_3_3 2 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  181 217 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 181 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 181 217))))))))))))))))))))))))))))))))))))) (allB_succ' 38 180 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 180 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 180 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 180 217 (Polychromatic418967fa.accept_19_17_9_8_1_3269 36 180
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 180 217 (accept_3_3 35 180
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 180 217
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 180 217 (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 180 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 180 217 (accept_3_3 32 180 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 180 217 (Polychromatic418967fa.accept_17_14_10_13_1_4147 31 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 180 217
  (Polychromatic418967fa.accept_14_2_12_7_1_617 30 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 180 217 (accept_3_3 29 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 180 217 (Polychromatic418967fa.accept_13_2_11_9_1_591 28 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 180 217 (Polychromatic418967fa.accept_13_1_11_9_1_1857 27 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 180 217 (accept_3_3 26 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 180 217 (Polychromatic418967fa.accept_21_4_12_7_1_5174 25 180
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 180 217
  (Polychromatic418967fa.accept_16_8_4_9_1_4666 24 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 180 217 (accept_3_3 23 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 180 217 (Polychromatic418967fa.accept_17_5_10_13_1_10558 22 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 180 217 (accept_3_3 20 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 180 217 (Polychromatic418967fa.accept_14_5_12_7_1_2767 19 180
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 217
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 217 (accept_3_3 17 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 180 217 (Polychromatic418967fa.accept_14_2_12_7_1_617 16 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 180 217 (Polychromatic418967fa.accept_13_2_11_9_1_591 15 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 180 217 (accept_3_3 14 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 180 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 217
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 180 217 (accept_3_3 11 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 180 217 (Polychromatic418967fa.accept_25_10_5_17_1_12924 10 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 180 217 (Polychromatic418967fa.accept_14_9_12_7_1_597 9 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 217 (accept_3_3 8 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 217 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 180 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 217
  (Polychromatic418967fa.accept_21_6_12_7_1_11386 6 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 180 217 (accept_3_3 5 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  180 217 (Polychromatic418967fa.accept_19_4_9_8_1_8794 4 180 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 180 217 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 180 217 (accept_3_3 2 180 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 180 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 217))))))))))))))))))))))))))))))))))))))
  (allB_succ' 39 179 217 (Eq.refl Bool.true) (allA_of_3_1 39 179 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 40 178 217 (Eq.refl Bool.true) (allA_succ_of_accept 39 178 217 (Polychromatic418967fa.accept_4_3_2_1_1_50
  39 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 178 217 (accept_3_3 38
  178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 178 217
  (Polychromatic418967fa.accept_17_3_8_13_1_5361 37 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 178 217 (Polychromatic418967fa.accept_15_6_13_7_1_222 36 178 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 178 217 (accept_3_3 35 178 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 178 217 (Polychromatic418967fa.accept_19_15_7_8_1_8755 34 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 178 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 178 217 (accept_3_3 32 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 178 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 178 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 178 217 (accept_3_3 29 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 178 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 178 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 178 217 (accept_3_3 26 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 178 217 (Polychromatic418967fa.accept_10_5_8_7_1_2174 25 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 178 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 178 217 (accept_3_3 23 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 178 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 178 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 178 217 (accept_3_3 20 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 178 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 178 217 (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 178 217 (accept_3_3 17 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 178 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 178
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 178 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 178 217 (accept_3_3 14 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 178 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 178 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 178 217 (accept_3_3 11 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 178 217 (Polychromatic418967fa.accept_18_10_16_1_1_1534 10 178 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 178 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 178 217 (accept_3_3 8 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  178 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 178 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 178 217 (accept_3_3 5 178 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 178 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 178 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 178 217 (accept_3_3 2 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  178 217 (Polychromatic418967fa.accept_16_1_2_9_1_1607 1 178 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 178 217)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 177 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 40 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 177 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 217 (accept_3_3 38 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  37 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 217
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 177 217 (accept_3_3 35 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 177 217 (Polychromatic418967fa.accept_13_7_8_9_1_1158 33 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 217 (accept_3_3 32 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 177 217 (accept_3_3 29 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 177 217 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 217 (accept_3_3 26 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 217
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 24 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 177 217 (accept_3_3 23 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 177 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 177 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 217 (accept_3_3 20 177 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 217 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 217
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 177 217 (accept_3_3 17 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 177 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 217 (accept_3_3 14 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 177 217 (accept_3_3 11 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 177 217 (Polychromatic418967fa.accept_25_9_2_17_1_12923 9 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 217 (accept_3_3 8 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 177 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 217
  (Polychromatic418967fa.accept_15_6_12_7_1_1360 6 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 177 217 (accept_3_3 5 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  177 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 177 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 177 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 177 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 217 (accept_3_3 2 177 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 217 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 177 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 217)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 176 217 (Eq.refl Bool.true) (allA_of_3_1 42 176 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 43 175 217 (Eq.refl Bool.true) (allA_succ_of_gcd 42 175 217 7 6 25 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 175 217 (accept_3_3 41 175 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 175 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 175
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 175 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 175 217 (accept_3_3 38 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 175 217 (Polychromatic418967fa.accept_19_18_4_8_1_3282 37 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 175 217 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 175 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 175 217 7 5 25 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 175 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 175 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 33 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 175 217 (accept_3_3 32 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 175 217 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 175 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 175 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 175 217 (accept_3_3 29 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  175 217 7 4 25 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 175 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 27 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 175 217 (accept_3_3 26 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 175 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 175 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 175 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 217 (accept_3_3 23 175 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22
  175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 175 217 7 3 25 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 175 217 (accept_3_3 20
  175 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 175 217
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 19 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 217 (accept_3_3 17 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 175 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 217 (Polychromatic418967fa.accept_9_6_4_1_1_390
  15 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 175 217 7 2 25 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 13 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 217 (accept_3_3 11 175 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 175 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 175 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 217 (Polychromatic418967fa.accept_11_9_10_8_1_444
  9 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 217 (accept_3_3 8
  175 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175 217 7 1 25 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 175 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 217 (accept_3_3 5 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 217 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 175 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 3 175 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 217 (accept_3_3 2 175 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 175 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 217)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 174 217 (Eq.refl Bool.true) (allA_succ_of_accept 43 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50
  43 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 174 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 174 217 (accept_3_3 41 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 174 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 217 (accept_3_3 38 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 174 217 (Polychromatic418967fa.accept_16_5_14_9_1_2572 37 174 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 174 217
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 174 217 (accept_3_3 35 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 174 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 174 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 217 (accept_3_3 32 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 174 217
  (Polychromatic418967fa.accept_13_4_5_9_1_1829 30 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 174 217 (accept_3_3 29 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 174 217 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 217 (accept_3_3 26 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 174 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 174 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 174 217 (accept_3_3 23 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 174 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 174 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 217 (accept_3_3 20 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 174 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 174 217
  (Polychromatic418967fa.accept_21_18_6_7_1_6751 18 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 174 217 (accept_3_3 17 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 174 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 217 (accept_3_3 14 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 174 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 174 217 (accept_3_3 11 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 174 217 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 174 217 (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 217 (accept_3_3 8 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 174 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 174 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 174 217 (accept_3_3 5 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  174 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 174 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 174 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 217 (accept_3_3 2 174 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 174 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 217))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 45 173 217 (Eq.refl Bool.true) (allA_of_3_1 45 173 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 46 172 217 (Eq.refl Bool.true) (allA_succ_of_accept 45 172 217 (Polychromatic418967fa.accept_6_3_4_1_1_8
  45 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 172 217 (accept_3_3 44
  172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 172 217
  (Polychromatic418967fa.accept_21_1_4_7_1_3689 43 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 172 217 (Polychromatic418967fa.accept_20_2_12_17_1_5547 42 172 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 172 217 (accept_3_3 41 172 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 172 217 (Polychromatic418967fa.accept_16_8_12_9_1_2569 40 172 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 172 217 (accept_3_3 38 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 172 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 172 217 (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 172 217 (accept_3_3 35 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 172 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 172
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 172 217 (accept_3_3 32 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 172 217 (Polychromatic418967fa.accept_13_5_3_9_1_1189 31 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 172 217 (Polychromatic418967fa.accept_19_11_1_8_1_10127 30 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 172 217 (accept_3_3 29 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 172 217 (Polychromatic418967fa.accept_13_2_3_9_1_2610 28 172
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 172 217 (accept_3_3 26 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 172 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 172 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 24 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 172 217 (accept_3_3 23 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 172 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 172
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 172 217 (accept_3_3 20 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 172 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 172 217 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 172 217 (accept_3_3 17 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 172 217 (Polychromatic418967fa.accept_18_16_10_1_1_3696 16 172
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 172 217 (accept_3_3 14 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 172 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 172 217 (Polychromatic418967fa.accept_13_12_3_9_1_4341 12 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 172 217 (accept_3_3 11 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 172
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 217 (accept_3_3 8 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 217 (Polychromatic418967fa.accept_13_7_3_9_1_1142 7 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 217 (Polychromatic418967fa.accept_13_6_3_9_1_1827 6 172 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 217 (accept_3_3 5 172 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 172 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 217 (accept_3_3 2 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 217 (Polychromatic418967fa.accept_17_1_2_13_1_2026 1 172 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 217)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 171 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 171 217 (Polychromatic418967fa.accept_12_9_3_1_1_303 45 171
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 171 217 (accept_3_3 44 171
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 217
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 43 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 217 (accept_3_3 41 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 171 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 217 (Polychromatic418967fa.accept_14_11_3_7_1_604
  39 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 217 (accept_3_3 38
  171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 217
  (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 171 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 217 (accept_3_3 35 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 217 (Polychromatic418967fa.accept_12_9_3_1_1_303
  33 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 217 (accept_3_3 32
  171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 217
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 217 (accept_3_3 29 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 171 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186
  27 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 217 (accept_3_3 26
  171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 217
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 171 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 217 (accept_3_3 23 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 217 (Polychromatic418967fa.accept_12_9_3_1_1_303
  21 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 217 (accept_3_3 20
  171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 217
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 217 (accept_3_3 17 171 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 171 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 217
  (Polychromatic418967fa.accept_21_15_3_7_1_6748 15 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 171 217 (accept_3_3 14 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 171 217 (Polychromatic418967fa.accept_15_13_6_7_1_1369 13 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 171 217 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 171 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 217 (accept_3_3 11 171 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 171 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 171 217 (accept_3_3 8 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  171 217 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 171 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 217 (accept_3_3 5 171 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 171 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 217
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 171 217 (accept_3_3 2 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  171 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 171 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 171 217))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 170 217 (Eq.refl
  Bool.true) (allA_of_3_1 48 170 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 49 169 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 48 169 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 169 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 169 217 (accept_3_3 47 169 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 169 217 (Polychromatic418967fa.accept_17_12_16_13_1_7951 46 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 169 217
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 169 217 (accept_3_3 44 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 169 217 (Polychromatic418967fa.accept_17_9_16_13_1_6636 43 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 169 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 42 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 169 217 (accept_3_3 41 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 217 (accept_3_3 38 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 217 (Polychromatic418967fa.accept_17_3_16_13_1_6635 37 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 217 (Polychromatic418967fa.accept_14_8_1_7_1_3725 36 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 217 (accept_3_3 35 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 169
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 217 (accept_3_3 32 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 217 (accept_3_3 29 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 217
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 27 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 217 (accept_3_3 26 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 217 (accept_3_3 23 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 217 (accept_3_3 20 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 217 (Polychromatic418967fa.accept_21_19_1_7_1_3724 19 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 217 (accept_3_3 17 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 217 (Polychromatic418967fa.accept_18_16_7_1_1_6332 16 169
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 217 (accept_3_3 14 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 217 (accept_3_3 11 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 169 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 217
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 9 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 217 (accept_3_3 8 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 217 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 217 (accept_3_3 5 169 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 169 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 217 (accept_3_3 2 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 169 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 217))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 168 217 (Eq.refl
  Bool.true) (allA_succ_of_gcd 49 168 217 7 7 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 48 168 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 168 217 (accept_3_3 47 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 168 217 (Polychromatic418967fa.accept_22_2_14_19_1_11310 46 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 168 217
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 168 217 (accept_3_3 44 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 168 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 168 217 7 6 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 168 217 (accept_3_3 41 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 168 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 168 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 168 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 168 217 (accept_3_3 38 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 217
  (Polychromatic418967fa.accept_19_18_16_8_1_12903 37 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 168 217 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 168 217 7 5 24 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 168 217
  (Polychromatic418967fa.accept_9_7_6_1_1_709 34 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 168 217 (Polychromatic418967fa.accept_16_1_8_9_1_3462 33 168 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 217 (accept_3_3 32 168 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 168 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 30
  168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 217 (accept_3_3 29
  168 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 217 7 4 24 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 217
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 168 217 (accept_3_3 26 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 168 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 168 217 (Polychromatic418967fa.accept_19_5_16_8_1_10057 24 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 217 (accept_3_3 23 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 217 7 3 24 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 217 (accept_3_3 20
  168 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 217
  (Polychromatic418967fa.accept_10_9_8_7_1_714 19 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 168 217 (Polychromatic418967fa.accept_19_18_16_8_1_12903 18 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 217 (accept_3_3 17 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 168 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 168 217
  (Polychromatic418967fa.accept_10_5_8_7_1_2174 15 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 168 217 7 2 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 168 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 168 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 217 (accept_3_3 11 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 168 217
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 168 217 (Polychromatic418967fa.accept_10_9_8_7_1_714 9 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 168 217 (accept_3_3 8 168 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 7 168 217 7 1 24 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 6 168 217 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 217 (accept_3_3 5 168 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 168 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 168 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 168 217 (accept_3_3 2 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  168 217 (Polychromatic418967fa.accept_16_1_8_9_1_3462 1 168 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 168 217)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 167 217 (Eq.refl
  Bool.true) (allA_of_3_1 51 167 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 52 166 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 51 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 166 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 166 217 (accept_3_3 50 166 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 166 217 (Polychromatic418967fa.accept_20_9_6_17_1_1654 49 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 166 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 166 217 (accept_3_3 47 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 166 217 (Polychromatic418967fa.accept_21_4_19_7_1_5142 46 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 166 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 166 217 (accept_3_3 44 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 166 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 166 217 (accept_3_3 41 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 166 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 166 217 (accept_3_3 38 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 166 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 166 217
  (Polychromatic418967fa.accept_15_6_1_7_1_4079 36 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 166 217 (accept_3_3 35 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 166 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 166 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 166 217 (accept_3_3 32 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 166 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 166 217 (accept_3_3 29 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 166 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 217 (accept_3_3 26 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 166 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 166 217 (accept_3_3 23 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 166 217 (Polychromatic418967fa.accept_19_3_14_8_1_3272 22 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 166 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 217 (accept_3_3 20 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 217
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 18 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 166 217 (accept_3_3 17 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 217 (accept_3_3 14 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 166 217 (accept_3_3 11 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 166 217 (Polychromatic418967fa.accept_15_10_1_7_1_5207 10 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 166 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 217 (accept_3_3 8 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 217 (accept_3_3 5 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 166 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 217 (accept_3_3 2 166 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 166 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166
  217)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 165 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 165 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 165 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 165 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 165 217 (accept_3_3 50 165 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 217 (Polychromatic418967fa.accept_9_4_3_1_1_154
  49 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 217
  (Polychromatic418967fa.accept_10_8_5_7_1_358 48 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 165 217 (accept_3_3 47 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 165 217 (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 165 217 (accept_3_3 44 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 165 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 165 217 (accept_3_3 41 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 165 217 (Polychromatic418967fa.accept_12_3_9_1_1_290 39 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 217 (accept_3_3 38 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 217 (Polychromatic418967fa.accept_19_18_13_8_1_10099 37
  165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 165 217 (accept_3_3 35 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 165 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 217 (accept_3_3 32 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 217
  (Polychromatic418967fa.accept_16_14_5_9_1_5901 30 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 165 217 (accept_3_3 29 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 165 217 (Polychromatic418967fa.accept_12_3_9_1_1_290 27 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 217 (accept_3_3 26 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 165 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 24 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 217 (accept_3_3 23 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 217 (Polychromatic418967fa.accept_19_2_13_8_1_8778 21 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 217 (accept_3_3 20 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 217 (Polychromatic418967fa.accept_21_19_18_7_1_8388 19 165
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 217
  (Polychromatic418967fa.accept_10_8_5_7_1_358 18 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 217 (accept_3_3 17 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 217 (accept_3_3 14 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 12 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 217 (accept_3_3 11 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 217 (Polychromatic418967fa.accept_18_9_3_1_1_2559 9 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 217 (accept_3_3 8 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 6 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 217 (accept_3_3 5 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  165 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 165 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 217 (accept_3_3 2 165 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 217 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 165 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  217))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 164 217 (Eq.refl Bool.true) (allA_of_3_1 54
  164 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 55 163 217 (Eq.refl Bool.true) (allA_succ_of_accept 54
  163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 163 217 (accept_3_3 53 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 163 217 (Polychromatic418967fa.accept_21_10_16_7_1_11388 52 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 163 217 (Polychromatic418967fa.accept_15_6_13_7_1_222
  51 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 163 217 (accept_3_3 50
  163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 163 217
  (Polychromatic418967fa.accept_25_24_13_17_1_7336 49 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 163 217 (Polychromatic418967fa.accept_17_14_10_13_1_4147 48 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 163 217 (accept_3_3 47 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 163 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 163 217
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 163 217 (accept_3_3 44 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 163 217 (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 163 217 (accept_3_3 41 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 163 217 (Polychromatic418967fa.accept_14_12_9_7_1_2762 40 163 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 163 217
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 39 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 163 217 (accept_3_3 38 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 163 217 (Polychromatic418967fa.accept_13_11_7_9_1_612 37 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 163 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 163 217 (accept_3_3 35 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 163 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 163 217
  (Polychromatic418967fa.accept_14_5_9_7_1_590 33 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 163 217 (accept_3_3 32 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 217 (Polychromatic418967fa.accept_17_14_10_13_1_4147 31 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 217 (accept_3_3 29 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 217 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 163
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 217
  (Polychromatic418967fa.accept_21_6_16_7_1_3714 27 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 217 (accept_3_3 26 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 217 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 217 (accept_3_3 23 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 163 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 217
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 217 (accept_3_3 20 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 217 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 217 (accept_3_3 17 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 217
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 217 (accept_3_3 14 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 217 (Polychromatic418967fa.accept_21_13_16_7_1_3712 13 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 217 (Polychromatic418967fa.accept_14_12_9_7_1_2762 12 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 217 (accept_3_3 11 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 163 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 217
  (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 217 (accept_3_3 8 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 217 (Polychromatic418967fa.accept_16_7_3_9_1_2557 7 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 217 (accept_3_3 5 163 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 4 163 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 217
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 3 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 217 (accept_3_3 2 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 217 (Polychromatic418967fa.accept_19_1_11_8_1_4504 1 163 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 217))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 162 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 162 217 (Polychromatic418967fa.accept_10_4_2_7_1_373
  54 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 162 217 (accept_3_3 53
  162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 217
  (Polychromatic418967fa.accept_20_12_2_17_1_1620 52 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 217 (accept_3_3 50 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 162 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 49 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 162 217
  (Polychromatic418967fa.accept_14_6_8_7_1_589 48 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 162 217 (accept_3_3 47 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 162 217 (Polychromatic418967fa.accept_13_7_6_9_1_1831 46 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 162 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 45 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 217 (accept_3_3 44 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 162 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 162 217
  (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 162 217 (accept_3_3 41 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 162 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 40 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 217 (accept_3_3 38 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 162 217 (Polychromatic418967fa.accept_19_18_10_8_1_2088 37 162 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 162 217
  (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 162 217 (accept_3_3 35 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 162 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 162 217 (Polychromatic418967fa.accept_13_7_6_9_1_1831 33 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 217 (accept_3_3 32 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 162 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 162 217
  (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 162 217 (accept_3_3 29 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 162 217 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 217 (accept_3_3 26 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 162 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 162 217
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 162 217 (accept_3_3 23 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 162 217 (Polychromatic418967fa.accept_16_6_2_9_1_5897 22 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 162 217 (Polychromatic418967fa.accept_15_6_12_7_1_1360 21 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 217 (accept_3_3 20 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 162 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 162 217
  (Polychromatic418967fa.accept_15_3_12_7_1_1346 18 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 162 217 (accept_3_3 17 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 162 217 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 217 (accept_3_3 14 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 217 (Polychromatic418967fa.accept_14_13_8_7_1_1224 13 162 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 162 217
  (Polychromatic418967fa.accept_16_12_2_9_1_3461 12 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 162 217 (accept_3_3 11 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 162 217 (Polychromatic418967fa.accept_13_10_6_9_1_1152 10 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 162 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 217 (accept_3_3 8 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 162 217
  (Polychromatic418967fa.accept_14_6_8_7_1_589 6 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 162 217 (accept_3_3 5 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  162 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 4 162 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 162 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 217 (accept_3_3 2 162 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 1 162 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 161 217 (Eq.refl Bool.true) (allA_of_3_1 57
  161 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 58 160 217 (Eq.refl Bool.true) (allA_succ_of_accept 57
  160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 160 217 (accept_3_3 56 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 160 217 (Polychromatic418967fa.accept_14_13_6_7_1_2013 55 160 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 160 217 (Polychromatic418967fa.accept_24_6_16_1_1_12922 54 160
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 160 217 (accept_3_3 53 160
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 160 217
  (Polychromatic418967fa.accept_21_10_13_7_1_6789 52 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 160 217 (accept_3_3 50 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 160 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 160 217 (accept_3_3 47 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 160 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 160 217 (accept_3_3 44 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 160 217 (Polychromatic418967fa.accept_14_1_6_7_1_1936 43 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 160 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 160 217 (accept_3_3 41 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 160 217 (accept_3_3 38 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 160 217 (Polychromatic418967fa.accept_21_16_13_7_1_8385 37 160 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 160 217
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 160 217 (accept_3_3 35 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 160 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 217 (accept_3_3 32 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 160 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 160 217 (accept_3_3 29 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 160 217 (Polychromatic418967fa.accept_17_11_7_13_1_11667 28 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 217 (accept_3_3 26 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 160 217 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 160
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 160 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 160 217 (accept_3_3 23 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 217 (accept_3_3 20 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 160 217 (Polychromatic418967fa.accept_13_6_4_9_1_4326 19 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 217
  (Polychromatic418967fa.accept_13_5_4_9_1_601 18 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 217 (accept_3_3 17 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 217 (Polychromatic418967fa.accept_15_1_10_7_1_4087 16 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 217 (accept_3_3 14 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 160 217 (accept_3_3 11 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 160 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 217 (accept_3_3 8 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 160 217 (Polychromatic418967fa.accept_13_7_4_9_1_1865 7 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 160 217 (accept_3_3 5 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  160 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 160 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 160 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 217 (accept_3_3 2 160 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 160 217 (Polychromatic418967fa.accept_14_1_6_7_1_1936 1 160 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 159 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 159 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 159 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 159 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 217 (accept_3_3 56 159 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 217
  (Polychromatic418967fa.accept_20_15_19_17_1_722 55 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 217 (accept_3_3 53 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 159 217
  (Polychromatic418967fa.accept_13_12_3_9_1_4341 51 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 159 217 (accept_3_3 50 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 159 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 159 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 217 (accept_3_3 47 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 159 217 (accept_3_3 44 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 159 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 217 (accept_3_3 41 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 159 217 (accept_3_3 38 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 159 217 (Polychromatic418967fa.accept_14_9_5_7_1_1251 37 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 159 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 217 (accept_3_3 35 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 159 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 33 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 159 217 (accept_3_3 32 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 159 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 217 (accept_3_3 29 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 217
  (Polychromatic418967fa.accept_20_7_19_17_1_2794 27 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 217 (accept_3_3 26 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 159 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 217 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 159
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 217 (accept_3_3 23 159
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2
  22 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 159 217 (accept_3_3 20 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 159 217 (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 217 (accept_3_3 17 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 217
  (Polychromatic418967fa.accept_13_2_3_9_1_2610 15 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 159 217 (accept_3_3 14 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 159 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 159 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 12 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 217 (accept_3_3 11 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 159 217 (accept_3_3 8 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  159 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 159 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 217 (accept_3_3 5 159 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 159 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 159 217 (accept_3_3 2 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  159 217 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 159 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 159 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 158 217
  (Eq.refl Bool.true) (allA_of_3_1 60 158 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 61 157 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 60 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 157 217 (accept_3_3 59 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 157 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 157 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 157 217 (accept_3_3 56 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 157 217 (Polychromatic418967fa.accept_16_7_13_9_1_1653 55 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 157 217 (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 157 217 (accept_3_3 53 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 52 157 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 157 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 157 217 (accept_3_3 50 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 157 217 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 157 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 157 217 (accept_3_3 47 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 157 217 (Polychromatic418967fa.accept_14_4_3_7_1_3702 46 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 157 217
  (Polychromatic418967fa.accept_13_6_1_9_1_619 45 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 157 217 (accept_3_3 44 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 157 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 157 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 42 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 157 217 (accept_3_3 41 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 157 217 (Polychromatic418967fa.accept_19_2_5_8_1_2081 40 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 157 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 157 217 (accept_3_3 38 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 157 217 (Polychromatic418967fa.accept_13_11_1_9_1_1179 37 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 217 (accept_3_3 35 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 157 217 (accept_3_3 32 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 157 217 (Polychromatic418967fa.accept_13_5_1_9_1_618 31 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 30 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 217 (accept_3_3 29 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 28 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 217
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 157 217 (accept_3_3 26 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 157 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 157 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 217 (accept_3_3 23 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 217 (Polychromatic418967fa.accept_16_6_13_9_1_4690 22 157 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 217 (accept_3_3 20 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 217 (Polychromatic418967fa.accept_13_5_1_9_1_618 18 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 217 (accept_3_3 17 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 157 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 217 (accept_3_3 14 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 217 (Polychromatic418967fa.accept_19_13_5_8_1_4487 13 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 217 (accept_3_3 11 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 217 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 157 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 217
  (Polychromatic418967fa.accept_17_9_4_13_1_3057 9 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 217 (accept_3_3 8 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 6 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 217 (accept_3_3 5 157 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 4 157 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 217 (accept_3_3 2 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 217 (Polychromatic418967fa.accept_16_1_13_9_1_2551 1 157 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 156 217
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 156 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 156 217 (accept_3_3 59 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 156 217 (Polychromatic418967fa.accept_15_12_6_7_1_1353 57 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 217 (accept_3_3 56 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 217 (Polychromatic418967fa.accept_17_4_3_13_1_6692 55 156
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 217
  (Polychromatic418967fa.accept_14_12_2_7_1_1243 54 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 156 217 (accept_3_3 53 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 156 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 156 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 156 217 (accept_3_3 50 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 217
  (Polychromatic418967fa.accept_19_10_4_8_1_11500 48 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 156 217 (accept_3_3 47 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 156 217 (Polychromatic418967fa.accept_15_1_6_7_1_6282 46 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 156 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 156 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 156 217 (accept_3_3 44 156 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 217 (Polychromatic418967fa.accept_9_7_3_1_1_386
  43 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 42 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 156 217 (accept_3_3 41 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 156 217 (Polychromatic418967fa.accept_18_3_12_1_1_3787 39 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 156 217 (accept_3_3 38 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 156 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 217
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 156 217 (accept_3_3 35 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 156 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 156 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 156 217 (accept_3_3 32 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 217
  (Polychromatic418967fa.accept_24_6_12_1_1_12921 30 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 156 217 (accept_3_3 29 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 217 (Polychromatic418967fa.accept_15_13_6_7_1_1369 28 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 156 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 156
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 156 217 (accept_3_3 26 156
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 217
  (Polychromatic418967fa.accept_9_7_3_1_1_386 25 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 156 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 217 (accept_3_3 23 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 156 217 (Polychromatic418967fa.accept_8_5_4_1_1_111
  21 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 156 217 (accept_3_3 20
  156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 217
  (Polychromatic418967fa.accept_14_5_2_7_1_2804 19 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 156 217 (Polychromatic418967fa.accept_16_2_12_9_1_2568 18 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 217 (accept_3_3 17 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 156 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 156 217 (Polychromatic418967fa.accept_9_6_3_1_1_155
  15 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 156 217 (accept_3_3 14
  156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 217
  (Polychromatic418967fa.accept_8_5_4_1_1_111 13 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 156 217 (Polychromatic418967fa.accept_14_12_2_7_1_1243 12 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 217 (accept_3_3 11 156 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 156 217 (Polychromatic418967fa.accept_17_10_3_13_1_6639 10 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 156 217
  (Polychromatic418967fa.accept_14_9_2_7_1_1242 9 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 156 217 (accept_3_3 8 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  156 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 156 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 217 (accept_3_3 5 156 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 156 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 156 217
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 3 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 156 217 (accept_3_3 2 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  156 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 156 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 155 217
  (Eq.refl Bool.true) (allA_of_3_1 63 155 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 64 154 217 (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 154 217 7 9 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 154 217 (accept_3_3 62 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 154 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 154 217 (Polychromatic418967fa.accept_13_8_11_9_1_593 60 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 154 217 (accept_3_3 59 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 154 217
  (Polychromatic418967fa.accept_19_1_2_8_1_10129 58 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 154 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 154 217 7 8 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55
  154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 154 217
  (Polychromatic418967fa.accept_13_2_11_9_1_591 54 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 154 217 (accept_3_3 53 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 154 217 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 154 217 (accept_3_3 50 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 49 154 217 7 7 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 48 154 217 (Polychromatic418967fa.accept_15_3_4_7_1_1352 48 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 154 217 (accept_3_3 47 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 154 217
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 46 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 154 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 154 217 (accept_3_3 44 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 154 217 7 6 22 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 154 217 (accept_3_3 41 154 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 154 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 154 217 (accept_3_3 38 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 154 217 (Polychromatic418967fa.accept_24_13_10_1_1_12920 37 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 217 (Polychromatic418967fa.accept_17_2_1_13_1_6670 36 154 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 154 217 7 5 22 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 154 217
  (Polychromatic418967fa.accept_13_8_11_9_1_593 34 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 154 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 217 (accept_3_3 32 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 217
  (Polychromatic418967fa.accept_19_11_2_8_1_8802 30 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 154 217 (accept_3_3 29 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  154 217 7 4 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 154 217 (accept_3_3 26 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 154 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 217 (Polychromatic418967fa.accept_19_5_2_8_1_8803 24 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 154 217 (accept_3_3 23 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 154 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 22 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 154 217 7 3 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 154 217 (accept_3_3 20 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 154 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 154 217 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 154 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 154 217 (accept_3_3 17 154 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 154 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 154 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 217 7 2 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 154 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 217 (Polychromatic418967fa.accept_10_2_4_7_1_352 12 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 154 217 (accept_3_3 11 154
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 154 217
  (Polychromatic418967fa.accept_15_10_4_7_1_3127 10 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 154 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 217 (accept_3_3 8 154 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 7 154 217 7 1 22 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 6 154 217 (Polychromatic418967fa.accept_19_6_2_8_1_4496 6 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 154 217 (accept_3_3 5 154 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 154 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 154 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 154 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 154 217 (accept_3_3 2 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  154 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 154 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 154 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 153 217
  (Eq.refl Bool.true) (allA_succ_of_accept 64 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 153 217 (accept_3_3 62 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 153 217 (Polychromatic418967fa.accept_22_17_21_19_1_4790 61 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 217 (Polychromatic418967fa.accept_18_6_9_1_1_3769 60 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 217 (accept_3_3 59 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 217
  (Polychromatic418967fa.accept_14_1_13_7_1_1205 57 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 217 (accept_3_3 56 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 153 217 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 217 (accept_3_3 53 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 217 (accept_3_3 50 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 153 217 (Polychromatic418967fa.accept_15_4_3_7_1_713 49 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 217 (Polychromatic418967fa.accept_14_6_13_7_1_2015 48 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 217 (accept_3_3 47 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 217
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 217 (accept_3_3 44 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 153 217 (Polychromatic418967fa.accept_14_1_13_7_1_1205 43 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 217 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 217 (accept_3_3 41 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 153 217 (accept_3_3 38 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 153 217 (Polychromatic418967fa.accept_19_18_1_8_1_7291 37 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 153 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 36 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 217 (accept_3_3 35 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 217
  (Polychromatic418967fa.accept_21_12_6_7_1_3739 33 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 153 217 (accept_3_3 32 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 153 217 (Polychromatic418967fa.accept_11_9_10_8_1_444 31 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 153 217 (Polychromatic418967fa.accept_19_11_1_8_1_10127 30 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 217 (accept_3_3 29 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 217 (accept_3_3 26 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 153 217 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 24 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 217 (accept_3_3 23 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 217
  (Polychromatic418967fa.accept_18_3_9_1_1_3690 21 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 153 217 (accept_3_3 20 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 153 217 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 153 217 (Polychromatic418967fa.accept_19_18_1_8_1_7291 18 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 217 (accept_3_3 17 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 217
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 15 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 217 (accept_3_3 14 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 153 217 (Polychromatic418967fa.accept_19_13_1_8_1_3281 13 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 217 (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 217 (accept_3_3 11 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 153 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 217
  (Polychromatic418967fa.accept_11_9_10_8_1_444 9 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 153 217 (accept_3_3 8 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  153 217 (Polychromatic418967fa.accept_19_7_1_8_1_7300 7 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 153 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 6 153 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 217 (accept_3_3 5 153 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 153 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 153 217 (accept_3_3 2 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  153 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 153 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 153 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 152 217
  (Eq.refl Bool.true) (allA_of_3_1 66 152 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 67 151 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 66 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 151 217 (accept_3_3 65 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 151 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 64 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 151 217
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 63 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 151 217 (accept_3_3 62 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 151 217 (Polychromatic418967fa.accept_16_13_7_9_1_2606 61 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 151 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 60 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 151 217 (accept_3_3 59 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 151 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 151 217 (accept_3_3 56 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 151 217 (Polychromatic418967fa.accept_13_3_8_9_1_1134 55 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 151 217 (accept_3_3 53 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 151 217 (Polychromatic418967fa.accept_14_10_11_7_1_1955 52 151 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 151 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 51 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 151 217 (accept_3_3 50 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 151 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 151 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 151 217 (accept_3_3 47 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 151 217
  (Polychromatic418967fa.accept_14_3_11_7_1_1260 45 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 151 217 (accept_3_3 44 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 151 217 (Polychromatic418967fa.accept_13_4_8_9_1_1156 43 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 217 (accept_3_3 41 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 39 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 217 (accept_3_3 38 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 217 (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 36 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 217 (accept_3_3 35 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 151 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 33 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 217 (accept_3_3 32 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 31 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 217 (accept_3_3 29 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 217 (Polychromatic418967fa.accept_17_11_15_13_1_11717 28 151 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 217
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 27 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 217 (accept_3_3 26 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 217 (Polychromatic418967fa.accept_13_12_8_9_1_1833 25 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 217 (accept_3_3 23 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 21 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 217 (accept_3_3 20 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 217 (Polychromatic418967fa.accept_16_3_7_9_1_3474 19 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 217 (accept_3_3 17 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 16 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 217 (accept_3_3 14 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 217 (accept_3_3 11 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 217
  (Polychromatic418967fa.accept_15_9_1_7_1_1350 9 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 217 (accept_3_3 8 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 217 (Polychromatic418967fa.accept_13_7_8_9_1_1158 7 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 217 (accept_3_3 5 151 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 151 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 217 (accept_3_3 2 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 217 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 151 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 150
  217 (Eq.refl Bool.true) (allA_succ_of_accept 67 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 150 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 150 217 (accept_3_3 65 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 150 217 (Polychromatic418967fa.accept_21_1_3_7_1_3727 64 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 217 (accept_3_3 62 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 150 217
  (Polychromatic418967fa.accept_13_8_7_9_1_611 60 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 150 217 (accept_3_3 59 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 150 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 150 217 (accept_3_3 56 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 150 217
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 150 217 (accept_3_3 53 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 150 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 150 217 (accept_3_3 50 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 150 217 (accept_3_3 47 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 150 217 (Polychromatic418967fa.accept_14_4_10_7_1_1946 46 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 150 217 (Polychromatic418967fa.accept_13_6_7_9_1_1848 45 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 150 217 (accept_3_3 44 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 150 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 150 217
  (Polychromatic418967fa.accept_13_3_7_9_1_1153 42 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 150 217 (accept_3_3 41 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 150 217 (accept_3_3 38 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 217 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 150 217
  (Polychromatic418967fa.accept_21_15_3_7_1_6748 36 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 150 217 (accept_3_3 35 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 150 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 150 217 (Polychromatic418967fa.accept_20_13_10_17_1_5510 33 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 217 (accept_3_3 32 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 150 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 150 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 150 217 (accept_3_3 29 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 150 217 (Polychromatic418967fa.accept_13_2_7_9_1_2616 28 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 217 (accept_3_3 26 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 150 217
  (Polychromatic418967fa.accept_13_11_7_9_1_612 24 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 150 217 (accept_3_3 23 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 150 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 21 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 150 217 (accept_3_3 20 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 217
  (Polychromatic418967fa.accept_14_4_10_7_1_1946 18 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 150 217 (accept_3_3 17 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 150 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 150 217 (accept_3_3 14 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 150 217 (accept_3_3 11 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 150 217 (Polychromatic418967fa.accept_17_10_14_13_1_12880 10 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 150 217 (Polychromatic418967fa.accept_18_9_6_1_1_3687 9 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 217 (accept_3_3 8 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 150 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 217
  (Polychromatic418967fa.accept_13_6_7_9_1_1848 6 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 150 217 (accept_3_3 5 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  150 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 150 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 150 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 150 217 (accept_3_3 2 150 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 217 (Polychromatic418967fa.accept_17_1_14_13_1_7966 1 150 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 149 217 (Eq.refl Bool.true)
  (allA_of_3_1 69 149 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 70 148 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 148 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 148 217 (accept_3_3 68 148 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 148 217 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 148 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 148 217 (accept_3_3 65 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 148 217 (Polychromatic418967fa.accept_19_7_15_8_1_1089 64 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 148 217 (accept_3_3 62 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 148 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 148 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 148 217 (accept_3_3 59 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 148 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 148 217 (accept_3_3 56 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 148 217 (Polychromatic418967fa.accept_10_5_8_7_1_2174 55 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 148 217
  (Polychromatic418967fa.accept_13_2_5_9_1_610 54 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 148 217 (accept_3_3 53 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 148 217 (accept_3_3 50 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 148 217 (Polychromatic418967fa.accept_10_9_8_7_1_714 49 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 148 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 148 217 (accept_3_3 47 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 148 217 (Polychromatic418967fa.accept_11_2_5_8_1_470 46 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 217 (accept_3_3 44 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 148 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 148 217 (accept_3_3 41 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 148 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 40 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 217 (accept_3_3 38 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 148 217
  (Polychromatic418967fa.accept_11_3_5_8_1_458 36 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 148 217 (accept_3_3 35 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 217 (accept_3_3 32 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 217 (Polychromatic418967fa.accept_19_12_15_8_1_10070 31 148 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 217 (accept_3_3 29 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 217 (Polychromatic418967fa.accept_13_2_5_9_1_610 28 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 27 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 217 (accept_3_3 26 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 217 (accept_3_3 23 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 217 (accept_3_3 20 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 217 (Polychromatic418967fa.accept_10_9_8_7_1_714 19 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 217
  (Polychromatic418967fa.accept_17_1_12_13_1_448 18 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 217 (accept_3_3 17 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 15 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 217 (accept_3_3 14 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 217 (accept_3_3 11 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 217 (accept_3_3 8 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 217 (accept_3_3 5 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 217 (Polychromatic418967fa.accept_13_4_5_9_1_1829 4 148 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 3 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 217 (accept_3_3 2 148 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 148 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 147 217 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 147 217 7 10 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 217 (accept_3_3 68 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 217 (accept_3_3 65 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 147 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 147 217 7 9 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 147 217 (accept_3_3 62 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 147 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 217 (accept_3_3 59 147 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 147 217 7 8 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 147 217 (Polychromatic418967fa.accept_15_10_12_7_1_1358 55 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 217 (accept_3_3 53
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 217
  (Polychromatic418967fa.accept_6_4_3_1_1_57 52 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 51 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 217 (accept_3_3 50 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 147 217 7 7 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 147 217 (Polychromatic418967fa.accept_15_3_12_7_1_1346 48 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 217 (accept_3_3 47 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 147 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 217
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 147 217 (accept_3_3 44 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 147 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 147 217 7 6 21 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 147 217 (accept_3_3 41 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 217 (Polychromatic418967fa.accept_16_7_3_9_1_2557 39 147
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 217 (accept_3_3 38 147
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 217
  (Polychromatic418967fa.accept_25_12_22_17_1_12919 37 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 147 217 (Polychromatic418967fa.accept_15_6_12_7_1_1360 36 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 147 217 7 5 21 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 147 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 34 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 33 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 147 217 (accept_3_3 32 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 147 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 217 (accept_3_3 29
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 147 217 7 4 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 147 217
  (Polychromatic418967fa.accept_18_9_3_1_1_2559 27 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 147 217 (accept_3_3 26 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 147 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 217 (accept_3_3 23 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 217 7 3 21 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 217 (accept_3_3 20 147 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 217 (Polychromatic418967fa.accept_13_6_4_9_1_4326
  19 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 147 217 (accept_3_3 17 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 147 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 15 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 147 217 7 2 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 147 217
  (Polychromatic418967fa.accept_9_4_3_1_1_154 13 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 147 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 217 (accept_3_3 11 147 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 147 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 147 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 147 217 (Polychromatic418967fa.accept_12_9_3_1_1_303 9
  147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 217 (accept_3_3 8 147
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 147 217 7 1 21 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 147 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 217 (accept_3_3 5 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  147 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 147 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 217 (Polychromatic418967fa.accept_15_3_12_7_1_1346 3 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 217 (accept_3_3 2 147 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 1 147 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 146 217 (Eq.refl Bool.true)
  (allA_of_3_1 72 146 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 73 145 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 145 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 145 217 (accept_3_3 71 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 145 217 (Polychromatic418967fa.accept_13_5_2_9_1_1195 70 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 145 217
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 69 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 145 217 (accept_3_3 68 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 145 217 (Polychromatic418967fa.accept_17_16_9_13_1_3087 67 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 145 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 66 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 145 217 (accept_3_3 65 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 145 217 (Polychromatic418967fa.accept_15_4_10_7_1_1356 64 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 145 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 145 217 (accept_3_3 62 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 145 217 (Polychromatic418967fa.accept_15_1_10_7_1_4087 61 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 145 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 145 217 (accept_3_3 59 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 145 217 (Polychromatic418967fa.accept_10_8_5_7_1_358 58 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 145 217
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 57 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 145 217 (accept_3_3 56 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 145 217 (Polychromatic418967fa.accept_13_3_2_9_1_1187 55 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 145 217 (Polychromatic418967fa.accept_14_12_5_7_1_2010 54 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 145 217 (accept_3_3 53 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 145 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 52 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 145 217
  (Polychromatic418967fa.accept_14_9_5_7_1_1251 51 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 145 217 (accept_3_3 50 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 145 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 49 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 145 217 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 145 217 (accept_3_3 47 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 217 (Polychromatic418967fa.accept_13_7_2_9_1_1826 46 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 217
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 45 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 217 (accept_3_3 44 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 42 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 217 (accept_3_3 41 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 40 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 217
  (Polychromatic418967fa.accept_17_5_9_13_1_1093 39 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 217 (accept_3_3 38 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 217 (Polychromatic418967fa.accept_13_11_2_9_1_2640 37 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 217 (Polychromatic418967fa.accept_21_15_19_7_1_6741 36 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 217 (accept_3_3 35 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 217 (Polychromatic418967fa.accept_15_4_10_7_1_1356 34 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 217 (accept_3_3 32 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 217 (Polychromatic418967fa.accept_13_5_2_9_1_1195 31 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 217 (Polychromatic418967fa.accept_14_2_5_7_1_3767 30 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 217 (accept_3_3 29 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 217 (Polychromatic418967fa.accept_10_8_5_7_1_358 28 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 217
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 217 (accept_3_3 26 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 217 (Polychromatic418967fa.accept_19_6_12_8_1_8798 25 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 217 (Polychromatic418967fa.accept_13_11_2_9_1_2640 24 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 217 (accept_3_3 23 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 22 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 217
  (Polychromatic418967fa.accept_16_5_1_9_1_4621 21 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 217 (accept_3_3 20 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 217 (Polychromatic418967fa.accept_13_6_2_9_1_1188 19 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 217 (Polychromatic418967fa.accept_10_8_5_7_1_358 18 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 217 (accept_3_3 17 145 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 217 (Polychromatic418967fa.accept_11_5_2_8_1_866 16 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 217
  (Polychromatic418967fa.accept_19_15_12_8_1_5922 15 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 145 217 (accept_3_3 14 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 145 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 217 (accept_3_3 11 145
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 217
  (Polychromatic418967fa.accept_16_10_1_9_1_4622 10 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 145 217 (Polychromatic418967fa.accept_14_9_5_7_1_1251 9 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 217 (accept_3_3 8 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 145 217 (Polychromatic418967fa.accept_13_7_2_9_1_1826 7 145 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 217 (Polychromatic418967fa.accept_13_6_2_9_1_1188
  6 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 217 (accept_3_3 5
  145 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 217
  (Polychromatic418967fa.accept_15_4_10_7_1_1356 4 145 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 3 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 217 (accept_3_3 2 145 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 145 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145
  217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 144 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 73 144 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 144 217 (Polychromatic418967fa.accept_10_2_4_7_1_352
  72 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 144 217 (accept_3_3 71
  144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 217
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 70 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 144 217 (Polychromatic418967fa.accept_19_12_11_8_1_2091 69 144 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 217 (accept_3_3 68 144 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 217 (Polychromatic418967fa.accept_13_2_1_9_1_1174 67 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 217
  (Polychromatic418967fa.accept_14_10_4_7_1_1214 66 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 144 217 (accept_3_3 65 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 144 217 (Polychromatic418967fa.accept_19_7_11_8_1_8743 64 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 63 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 217 (accept_3_3 62 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 144 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 61 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 144 217
  (Polychromatic418967fa.accept_13_8_1_9_1_1178 60 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 144 217 (accept_3_3 59 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 144 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 58 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 144 217 (Polychromatic418967fa.accept_13_5_1_9_1_618 57 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 217 (accept_3_3 56 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 144 217 (Polychromatic418967fa.accept_17_4_8_13_1_7960 55 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 144 217
  (Polychromatic418967fa.accept_13_2_1_9_1_1174 54 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 144 217 (accept_3_3 53 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 144 217 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 144 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 51 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 217 (accept_3_3 50 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 144 217 (Polychromatic418967fa.accept_13_10_1_9_1_3380 49 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 144 217
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 48 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 144 217 (accept_3_3 47 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 144 217 (Polychromatic418967fa.accept_15_1_9_7_1_3130 46 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 144 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 45 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 217 (accept_3_3 44 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 144 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 42 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 144 217 (accept_3_3 41 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 144 217 (Polychromatic418967fa.accept_19_2_11_8_1_2090 40 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 144 217 (Polychromatic418967fa.accept_14_11_4_7_1_609 39 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 217 (accept_3_3 38 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 37 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 144 217
  (Polychromatic418967fa.accept_13_10_1_9_1_3380 36 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 144 217 (accept_3_3 35 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 144 217 (Polychromatic418967fa.accept_13_8_1_9_1_1178 34 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 33 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 217 (accept_3_3 32 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 144 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 31 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 144 217
  (Polychromatic418967fa.accept_21_9_18_7_1_5180 30 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 144 217 (accept_3_3 29 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 144 217 (Polychromatic418967fa.accept_13_2_1_9_1_1174 28 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 144 217 (Polychromatic418967fa.accept_20_7_4_17_1_4132 27 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 217 (accept_3_3 26 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 217 (Polychromatic418967fa.accept_14_11_4_7_1_609 25 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 144 217
  (Polychromatic418967fa.accept_13_11_1_9_1_1179 24 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 144 217 (accept_3_3 23 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 144 217 (Polychromatic418967fa.accept_10_2_4_7_1_352 22 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 144 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 21 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 217 (accept_3_3 20 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 217 (Polychromatic418967fa.accept_13_6_1_9_1_619 19 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 144 217
  (Polychromatic418967fa.accept_13_5_1_9_1_618 18 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 144 217 (accept_3_3 17 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 144 217 (Polychromatic418967fa.accept_15_1_9_7_1_3130 16 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 144 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 217 (accept_3_3 14 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 13 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 144 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 12 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 144 217 (accept_3_3 11 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 144 217 (Polychromatic418967fa.accept_13_10_1_9_1_3380 10 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 144 217 (Polychromatic418967fa.accept_19_9_11_8_1_10050 9 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 217 (accept_3_3 8 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 217 (Polychromatic418967fa.accept_19_7_11_8_1_8743 7 144
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 144 217
  (Polychromatic418967fa.accept_13_6_1_9_1_619 6 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 144 217 (accept_3_3 5 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  144 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 144 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 144 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 3 144 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 217 (accept_3_3 2 144 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 144 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 143 217 (Eq.refl
  Bool.true) (allA_of_3_1 75 143 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 76 142 217 (Eq.refl Bool.true)
  (allA_succ_of_accept 75 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 142 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 142 217 (accept_3_3 74 142 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 142 217 (Polychromatic418967fa.accept_13_8_12_9_1_1168 73 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 142 217
  (Polychromatic418967fa.accept_20_12_2_17_1_1620 72 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 142 217 (accept_3_3 71 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 142 217 (Polychromatic418967fa.accept_17_2_6_13_1_2056 70 142 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 142 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 142 217 (accept_3_3 68 142 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 142 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 142 217 (accept_3_3 65 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 142 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 142 217 (accept_3_3 62 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 142 217 (Polychromatic418967fa.accept_14_5_2_7_1_2804 61 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 142 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 142 217 (accept_3_3 59 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 142 217 (accept_3_3 56 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 142 217
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 142 217 (accept_3_3 53 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 142 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 52 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 142 217 (accept_3_3 50 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 142 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 142 217 (accept_3_3 47 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 142 217 (Polychromatic418967fa.accept_18_10_16_1_1_1534 46 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 142 217 (accept_3_3 44 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 142 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 142 217 (accept_3_3 41 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 217 (accept_3_3 38 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 217 (Polychromatic418967fa.accept_14_9_2_7_1_1242 37 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 217
  (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 142 217 (accept_3_3 35 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 142 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 34 142 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 142 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 217 (accept_3_3 32 142 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 217 (accept_3_3 29 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 217 (accept_3_3 26 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 25 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 24 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 217 (accept_3_3 23 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 217 (accept_3_3 20 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 217
  (Polychromatic418967fa.accept_19_18_9_8_1_3267 18 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 217 (accept_3_3 17 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 16 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 217 (accept_3_3 14 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 12 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 217 (accept_3_3 11 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 217 (Polychromatic418967fa.accept_13_10_12_9_1_1837 10 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 217 (accept_3_3 8 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 6 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 217 (accept_3_3 5 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 142 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 217 (accept_3_3 2 142 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 217 (Polychromatic418967fa.accept_19_1_9_8_1_4474 1 142 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 141 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 141 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 75
  141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 217 (accept_3_3 74
  141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 217
  (Polychromatic418967fa.accept_13_8_11_9_1_593 73 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 141 217 (Polychromatic418967fa.accept_13_7_11_9_1_1858 72 141 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 217 (accept_3_3 71 141 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 217
  (Polychromatic418967fa.accept_14_13_1_7_1_1211 69 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 141 217 (accept_3_3 68 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 141 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 141 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 66 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 217 (accept_3_3 65 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 141 217 (accept_3_3 62 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 141 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 61 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 141 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 217 (accept_3_3 59 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 57 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 141 217 (accept_3_3 56 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 141 217 (Polychromatic418967fa.accept_14_13_1_7_1_1211 55 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 141 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 54 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 217 (accept_3_3 53 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 141 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 51 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 141 217 (accept_3_3 50 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 141 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 141 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 48 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 217 (accept_3_3 47 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 217
  (Polychromatic418967fa.accept_21_3_15_7_1_5155 45 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 141 217 (accept_3_3 44 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 141 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 141 217 (Polychromatic418967fa.accept_15_12_6_7_1_1353 42 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 217 (accept_3_3 41 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 141 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 39 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 141 217 (accept_3_3 38 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 141 217 (Polychromatic418967fa.accept_16_5_13_9_1_2594 37 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 141 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 36 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 217 (accept_3_3 35 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 217
  (Polychromatic418967fa.accept_13_7_11_9_1_1858 33 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 141 217 (accept_3_3 32 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 141 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 141 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 30 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 217 (accept_3_3 29 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 141 217 (accept_3_3 26 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 141 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 141 217 (Polychromatic418967fa.accept_10_4_1_7_1_371 24 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 217 (accept_3_3 23 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 141 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 21 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 141 217 (accept_3_3 20 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 141 217 (Polychromatic418967fa.accept_21_19_15_7_1_3709 19 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 141 217 (Polychromatic418967fa.accept_20_18_1_17_1_4085 18 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 217 (accept_3_3 17 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 141 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 15 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 141 217 (accept_3_3 14 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 141 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 13 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 141 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 217 (accept_3_3 11 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 217
  (Polychromatic418967fa.accept_17_9_5_13_1_2033 9 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 141 217 (accept_3_3 8 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  141 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 141 217 (Polychromatic418967fa.accept_10_6_1_7_1_342 6 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 217 (accept_3_3 5 141 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 141 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 3 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 141 217 (accept_3_3 2 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  141 217 (Polychromatic418967fa.accept_13_1_11_9_1_1857 1 141 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 141 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  78 140 217 (Eq.refl Bool.true) (allA_of_3_1 78 140 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 79 139 217
  (Eq.refl Bool.true) (allA_succ_of_accept 78 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 139 217 (accept_3_3 77 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 139 217 (Polychromatic418967fa.accept_14_6_13_7_1_2015 76 139
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 139 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 75 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 139 217 (accept_3_3 74 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 139 217 (Polychromatic418967fa.accept_19_16_6_8_1_8772 73 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 139 217 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 139 217 (accept_3_3 71 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 139 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 139 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 69 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 139 217 (accept_3_3 68 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 139 217 (Polychromatic418967fa.accept_17_16_3_13_1_2052 67 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 139 217 (accept_3_3 65 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 139 217 (Polychromatic418967fa.accept_14_8_13_7_1_2798 64 139 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 139 217
  (Polychromatic418967fa.accept_15_3_4_7_1_1352 63 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 139 217 (accept_3_3 62 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 139 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 60 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 139 217 (accept_3_3 59 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 139 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 57 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 139 217 (accept_3_3 56 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 55 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 217 (accept_3_3 53 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 51 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 217 (accept_3_3 50 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 217 (Polychromatic418967fa.accept_29_20_23_14_1_12879 49 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 139 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 48 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 217 (accept_3_3 47 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 139 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 217
  (Polychromatic418967fa.accept_19_7_6_8_1_12854 45 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 217 (accept_3_3 44 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 43 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 217 (accept_3_3 41 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 40 139 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 39 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 217 (accept_3_3 38 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 217 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 217 (Polychromatic418967fa.accept_14_8_13_7_1_2798 36 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 217 (accept_3_3 35 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 139 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 33 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 217 (accept_3_3 32 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 217 (Polychromatic418967fa.accept_19_12_6_8_1_12868 31 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 217 (accept_3_3 29 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 28 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 217
  (Polychromatic418967fa.accept_15_12_4_7_1_3097 27 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 217 (accept_3_3 26 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 217 (Polychromatic418967fa.accept_9_6_4_1_1_390 24 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 217 (accept_3_3 23 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 21 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 217 (accept_3_3 20 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 217 (Polychromatic418967fa.accept_21_19_13_7_1_3706 19 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 217 (accept_3_3 17 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 15 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 217 (accept_3_3 14 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 217 (Polychromatic418967fa.accept_19_13_6_8_1_8741 13 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 217 (Polychromatic418967fa.accept_9_3_4_1_1_22 12 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 217 (accept_3_3 11 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 217
  (Polychromatic418967fa.accept_21_9_13_7_1_5154 9 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 217 (accept_3_3 8 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 7 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 217 (accept_3_3 5 139 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 217 (Polychromatic418967fa.accept_11_4_7_8_1_1926 4 139 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 3 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 217 (accept_3_3 2 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 217 (Polychromatic418967fa.accept_14_1_13_7_1_1205 1 139 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 138 217 (Eq.refl Bool.true) (allA_succ_of_accept 79 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50
  79 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 138 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 78 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 138 217 (accept_3_3 77 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 76 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 217 (accept_3_3 74 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 138 217 (Polychromatic418967fa.accept_19_16_5_8_1_3253 73 138 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 138 217
  (Polychromatic418967fa.accept_13_7_8_9_1_1158 72 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 138 217 (accept_3_3 71 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 70 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 138 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 69 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 217 (accept_3_3 68 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 67 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 138 217
  (Polychromatic418967fa.accept_13_1_8_9_1_1154 66 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 138 217 (accept_3_3 65 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 138 217 (Polychromatic418967fa.accept_13_12_8_9_1_1833 64 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 217 (accept_3_3 62 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 138 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 60 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 138 217 (accept_3_3 59 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 58 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 138 217 (Polychromatic418967fa.accept_15_12_3_7_1_4123 57 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 217 (accept_3_3 56 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 138 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 138 217
  (Polychromatic418967fa.accept_19_16_5_8_1_3253 54 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 138 217 (accept_3_3 53 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 52 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 217 (accept_3_3 50 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 138 217
  (Polychromatic418967fa.accept_19_10_5_8_1_11588 48 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 217 (accept_3_3 47 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 138 217 (Polychromatic418967fa.accept_13_7_8_9_1_1158 46 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 217 (Polychromatic418967fa.accept_10_5_8_7_1_2174 45 138
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 217 (accept_3_3 44 138
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 43 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 138 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 217 (accept_3_3 41 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 40 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39
  138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 217 (accept_3_3 38
  138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 217
  (Polychromatic418967fa.accept_13_11_8_9_1_1161 37 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 138 217 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 138 217 (accept_3_3 35 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 34 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 217 (Polychromatic418967fa.accept_9_6_3_1_1_155
  33 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 217 (accept_3_3 32
  138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 31 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 138 217 (Polychromatic418967fa.accept_13_4_8_9_1_1156 30 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 138 217 (accept_3_3 29 138 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 138 217 (Polychromatic418967fa.accept_25_3_13_17_1_12918 28 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 27 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 138 217 (accept_3_3 26 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 138 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 138 217 (accept_3_3 23 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 22 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 217
  (Polychromatic418967fa.accept_18_3_12_1_1_3787 21 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 138 217 (accept_3_3 20 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 138 217 (Polychromatic418967fa.accept_17_1_2_13_1_2026 18 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 138 217 (accept_3_3 17 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 16 138 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 15 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 138 217 (accept_3_3 14 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 138 217 (Polychromatic418967fa.accept_13_12_8_9_1_1833 12 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 138 217 (accept_3_3 11 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 217 (Polychromatic418967fa.accept_15_10_3_7_1_715 10 138
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 217
  (Polychromatic418967fa.accept_10_9_8_7_1_714 9 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 138 217 (accept_3_3 8 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  138 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 138 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 138 217 (accept_3_3 5 138 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 4 138 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 3 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 138 217 (accept_3_3 2 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  138 217 (Polychromatic418967fa.accept_13_1_8_9_1_1154 1 138 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 137 217 (Eq.refl Bool.true) (allA_of_3_1 81 137 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 82 136 217 (Eq.refl Bool.true) (allA_succ_of_accept 81 136 217 (Polychromatic418967fa.accept_6_3_4_1_1_8
  81 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 136 217 (accept_3_3 80
  136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 136 217
  (Polychromatic418967fa.accept_13_1_6_9_1_1197 79 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 136 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 78 136 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 136 217 (accept_3_3 77 136 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 136 217 (Polychromatic418967fa.accept_16_12_8_9_1_2583 76 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 75 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 136 217 (accept_3_3 74 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 136 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 73 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 136 217 (Polychromatic418967fa.accept_13_7_6_9_1_1831 72 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 136 217 (accept_3_3 71 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 136 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 69 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 136 217 (accept_3_3 68 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 136 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 67 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 136 217 (Polychromatic418967fa.accept_13_1_6_9_1_1197 66 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 136 217 (accept_3_3 65 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 136 217 (Polychromatic418967fa.accept_21_1_10_7_1_11382 64 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 63 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 136 217 (accept_3_3 62 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 136 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 61 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 136 217 (Polychromatic418967fa.accept_14_4_10_7_1_1946 60 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 136 217 (accept_3_3 59 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 136 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 58 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 57 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 136 217 (accept_3_3 56 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 136 217 (Polychromatic418967fa.accept_13_3_6_9_1_1150 55 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 136 217 (Polychromatic418967fa.accept_13_2_6_9_1_2636 54 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 136 217 (accept_3_3 53 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 136 217 (Polychromatic418967fa.accept_16_4_8_9_1_4639 52 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 51 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 136 217 (accept_3_3 50 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 136 217 (Polychromatic418967fa.accept_13_10_6_9_1_1152 49 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 136 217 (Polychromatic418967fa.accept_23_2_21_10_1_9588 48 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 136 217 (accept_3_3 47 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 136 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 45 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 136 217 (accept_3_3 44 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 136 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 43 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 136 217 (Polychromatic418967fa.accept_13_3_6_9_1_1150 42 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 217 (accept_3_3 41 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 136 217 (Polychromatic418967fa.accept_11_7_4_8_1_1371 40 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 39 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 136 217 (accept_3_3 38 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 136 217 (Polychromatic418967fa.accept_21_16_10_7_1_3782 37 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 136 217 (Polychromatic418967fa.accept_13_10_6_9_1_1152 36 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 217 (accept_3_3 35 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 136 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 33 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 136 217 (accept_3_3 32 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 136 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 31 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 136 217 (Polychromatic418967fa.accept_13_4_6_9_1_3401 30 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 217 (accept_3_3 29 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 136 217 (Polychromatic418967fa.accept_13_2_6_9_1_2636 28 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 217 (accept_3_3 26 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 217 (Polychromatic418967fa.accept_14_11_10_7_1_1948 25 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 217 (Polychromatic418967fa.accept_15_9_1_7_1_1350 24 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 217 (accept_3_3 23 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 22 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 217 (accept_3_3 20 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 217 (Polychromatic418967fa.accept_20_19_16_17_1_5473 19 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 217 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 217 (accept_3_3 17 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 217 (Polychromatic418967fa.accept_13_3_6_9_1_1150 16 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 217 (accept_3_3 14 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 217 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 217 (accept_3_3 11 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 136
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 217 (accept_3_3 8 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 217 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 217 (Polychromatic418967fa.accept_15_6_1_7_1_4079 6 136 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 217 (accept_3_3 5 136 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 217 (Polychromatic418967fa.accept_13_4_6_9_1_3401 4 136 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 217 (accept_3_3 2 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1 136 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 83 135 217 (Eq.refl Bool.true) (allA_succ_of_accept 82 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2
  82 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 81 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 135 217 (accept_3_3 80 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 135 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 79 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 78 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 217 (accept_3_3 77 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 135 217
  (Polychromatic418967fa.accept_14_5_9_7_1_590 75 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 135 217 (accept_3_3 74 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 135 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 73 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 72 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 217 (accept_3_3 71 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 69 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 135 217 (accept_3_3 68 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 135 217 (Polychromatic418967fa.accept_13_2_5_9_1_610 67 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 66 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 217 (accept_3_3 65 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 63 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 135 217 (accept_3_3 62 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 135 217 (Polychromatic418967fa.accept_11_6_3_8_1_843 61 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 135 217 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 217 (accept_3_3 59 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 57 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 135 217 (accept_3_3 56 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 135 217 (Polychromatic418967fa.accept_13_3_5_9_1_5285 55 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 54 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 217 (accept_3_3 53 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 217
  (Polychromatic418967fa.accept_16_3_7_9_1_3474 51 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 135 217 (accept_3_3 50 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 135 217 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 135 217 (Polychromatic418967fa.accept_10_8_5_7_1_358 48 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 217 (accept_3_3 47 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 45 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 135 217 (accept_3_3 44 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 135 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 43 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 42 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 217 (accept_3_3 41 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 217
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 135 217 (accept_3_3 38 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 135 217 (Polychromatic418967fa.accept_17_3_16_13_1_6635 37 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 135 217 (Polychromatic418967fa.accept_21_15_9_7_1_3780 36 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 217 (accept_3_3 35 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 33 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 135 217 (accept_3_3 32 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 135 217 (Polychromatic418967fa.accept_21_10_9_7_1_9857 31 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 30 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 217 (accept_3_3 29 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 217
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 135 217 (accept_3_3 26 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 135 217 (Polychromatic418967fa.accept_19_6_2_8_1_4496 25 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 135 217 (Polychromatic418967fa.accept_16_8_7_9_1_7052 24 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 217 (accept_3_3 23 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 21 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 135 217 (accept_3_3 20 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 135 217 (Polychromatic418967fa.accept_14_5_9_7_1_590 19 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 217 (accept_3_3 17 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 217
  (Polychromatic418967fa.accept_13_2_5_9_1_610 15 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 135 217 (accept_3_3 14 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 135 217 (Polychromatic418967fa.accept_10_3_5_7_1_330 13 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 135 217 (Polychromatic418967fa.accept_10_2_5_7_1_1124 12 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 217 (accept_3_3 11 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 135 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 217
  (Polychromatic418967fa.accept_12_9_3_1_1_303 9 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 217 (accept_3_3 8 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  135 217 (Polychromatic418967fa.accept_22_7_3_19_1_8158 7 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 217 (accept_3_3 5 135 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 135 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 217
  (Polychromatic418967fa.accept_10_3_5_7_1_330 3 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 135 217 (accept_3_3 2 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  135 217 (Polychromatic418967fa.accept_13_1_5_9_1_226 1 135 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 135 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 84 134 217 (Eq.refl Bool.true) (allA_of_3_1 84 134 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 85 133 217 (Eq.refl Bool.true) (allA_succ_of_gcd 84 133 217 7 12 19 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 133 217 (accept_3_3 83 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 133 217 (Polychromatic418967fa.accept_22_16_1_19_1_12917 82
  133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 133 217
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 133 217 (accept_3_3 80 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 133 217 (Polychromatic418967fa.accept_24_7_13_1_1_9522 79 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 78 133 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 77 133 217 7 11 19 31 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 76 133 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 76 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 133 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 75 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 133 217 (accept_3_3 74 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 133 217 (Polychromatic418967fa.accept_13_8_3_9_1_5269 73 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 133 217
  (Polychromatic418967fa.accept_13_7_3_9_1_1142 72 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 133 217 (accept_3_3 71 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  133 217 7 10 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 69 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 133 217 (accept_3_3 68 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 133 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 133 217 (Polychromatic418967fa.accept_9_3_7_1_1_143
  66 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 133 217 (accept_3_3 65
  133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 133 217
  (Polychromatic418967fa.accept_10_4_3_7_1_1110 64 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 133 217 7 9 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 133 217 (accept_3_3 62 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 217 (Polychromatic418967fa.accept_16_13_5_9_1_4682 61 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 133 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 60 133 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 217 (accept_3_3 59 133 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 57 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 133 217 7 8 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 133 217 (Polychromatic418967fa.accept_10_5_3_7_1_1108 55 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 54 133
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 217 (accept_3_3 53 133
  217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 52 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 51 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 217 (accept_3_3 50 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 133 217 7 7 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 133 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 48 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 217 (accept_3_3 47 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 46 133
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 217
  (Polychromatic418967fa.accept_10_5_3_7_1_1108 45 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 217 (accept_3_3 44 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 217 (Polychromatic418967fa.accept_16_11_5_9_1_1617 43 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 133 217 7 6 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 133 217 (accept_3_3 41 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 39 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 217 (accept_3_3 38 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 217 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  37 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 217
  (Polychromatic418967fa.accept_8_4_5_1_1_299 36 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 133 217 7 5 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 133 217 (Polychromatic418967fa.accept_10_4_3_7_1_1110 34 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 33 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 217 (accept_3_3 32 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379
  31 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 30 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 133 217 (accept_3_3 29 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28
  133 217 7 4 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  27 133 217 (Polychromatic418967fa.accept_16_11_5_9_1_1617 27 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 133 217 (accept_3_3 26 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 133 217 (Polychromatic418967fa.accept_10_5_3_7_1_1108 25 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 217 (accept_3_3 23 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379
  22 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 133 217 7 3 19 31
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 133 217
  (accept_3_3 20 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 217
  (Polychromatic418967fa.accept_13_6_3_9_1_1827 19 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 217 (Polychromatic418967fa.accept_13_5_3_9_1_1189 18 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 217 (accept_3_3 17 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 217 (Polychromatic418967fa.accept_10_6_3_7_1_2197 16 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 15 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 133 217 7 2 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 133 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 13 133 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 217 (accept_3_3 11 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 217
  (Polychromatic418967fa.accept_17_10_14_13_1_12880 10 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 217 (Polychromatic418967fa.accept_15_9_13_7_1_1361 9 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 217 (accept_3_3 8 133 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 133 217 7 1 19 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 133 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 217 (accept_3_3 5 133 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 217 (Polychromatic418967fa.accept_8_4_5_1_1_299 4
  133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 3 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 217 (accept_3_3 2 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 217 (Polychromatic418967fa.accept_16_1_5_9_1_1649 1 133 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 86 132 217 (Eq.refl Bool.true) (allA_succ_of_accept 85 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111
  85 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 132 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 84 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 132 217 (accept_3_3 83 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 132 217 (Polychromatic418967fa.accept_20_2_12_17_1_5547 82 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 132 217 (Polychromatic418967fa.accept_13_3_2_9_1_1187 81 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 217 (accept_3_3 80 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 79 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 132 217
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 78 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 132 217 (accept_3_3 77 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 76 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 132 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 75 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 217 (accept_3_3 74 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 132 217 (Polychromatic418967fa.accept_19_16_18_8_1_8784 73 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 132 217
  (Polychromatic418967fa.accept_13_7_2_9_1_1826 72 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 132 217 (accept_3_3 71 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 70 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 69 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 217 (accept_3_3 68 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 67 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 132 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 66 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 132 217 (accept_3_3 65 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 132 217 (Polychromatic418967fa.accept_10_4_2_7_1_373 64 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 132 217 (Polychromatic418967fa.accept_13_11_2_9_1_2640 63 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 217 (accept_3_3 62 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 61 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 132 217
  (Polychromatic418967fa.accept_16_12_4_9_1_4633 60 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 132 217 (accept_3_3 59 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 58 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 132 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 57 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 217 (accept_3_3 56 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 55 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 132 217
  (Polychromatic418967fa.accept_10_4_2_7_1_373 54 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 132 217 (accept_3_3 53 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 52 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 132 217 (Polychromatic418967fa.accept_15_6_12_7_1_1360 51 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 217 (accept_3_3 50 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 49 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 132 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 48 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 132 217 (accept_3_3 47 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 132 217 (Polychromatic418967fa.accept_13_7_2_9_1_1826 46 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 45 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 217 (accept_3_3 44 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 43 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 132 217
  (Polychromatic418967fa.accept_13_3_2_9_1_1187 42 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 132 217 (accept_3_3 41 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 40 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 132 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 39 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 217 (accept_3_3 38 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 132 217
  (Polychromatic418967fa.accept_14_8_6_7_1_1934 36 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 132 217 (accept_3_3 35 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 34 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 132 217 (Polychromatic418967fa.accept_13_7_2_9_1_1826 33 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 217 (accept_3_3 32 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 31 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 132 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 30 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 132 217 (accept_3_3 29 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 132 217 (Polychromatic418967fa.accept_16_12_4_9_1_4633 28 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 132 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 27 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 217 (accept_3_3 26 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 25 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 132 217
  (Polychromatic418967fa.accept_10_4_2_7_1_373 24 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 132 217 (accept_3_3 23 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 22 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 21 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 217 (accept_3_3 20 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 19 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 132 217
  (Polychromatic418967fa.accept_13_5_2_9_1_1195 18 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 132 217 (accept_3_3 17 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 16 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 132 217 (Polychromatic418967fa.accept_10_5_2_7_1_345 15 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 217 (accept_3_3 14 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 132 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 132 217
  (Polychromatic418967fa.accept_9_3_6_1_1_24 12 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 132 217 (accept_3_3 11 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 132 217 (Polychromatic418967fa.accept_15_10_12_7_1_1358 10 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 132 217 (Polychromatic418967fa.accept_10_9_2_7_1_1096 9 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 217 (accept_3_3 8 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 217 (Polychromatic418967fa.accept_9_7_6_1_1_709 7 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 132 217
  (Polychromatic418967fa.accept_13_6_2_9_1_1188 6 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 132 217 (accept_3_3 5 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  132 217 (Polychromatic418967fa.accept_9_4_6_1_1_393 4 132 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 132 217 (Polychromatic418967fa.accept_9_3_6_1_1_24 3 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 217 (accept_3_3 2 132 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 217 (Polychromatic418967fa.accept_13_1_2_9_1_1186 1 132 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 131 217
  (Eq.refl Bool.true) (allA_of_3_1 87 131 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 88 130 217 (Eq.refl
  Bool.true) (allA_succ_of_accept 87 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 130 217 (accept_3_3 86 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 85 130 217 (Polychromatic418967fa.accept_19_9_16_8_1_2097 85 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 130 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 84 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 130 217 (accept_3_3 83 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 130 217 (Polychromatic418967fa.accept_19_6_16_8_1_10116 82 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 130 217 (accept_3_3 80 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 130 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 78 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 130 217 (accept_3_3 77 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 130 217 (Polychromatic418967fa.accept_11_10_9_8_1_1974 76 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 75 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 130 217 (accept_3_3 74 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 130 217 (Polychromatic418967fa.accept_14_3_4_7_1_175 73 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 130 217
  (Polychromatic418967fa.accept_15_12_10_7_1_1357 72 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 130 217 (accept_3_3 71 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 70 130 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 130 217 (accept_3_3 68 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 67
  130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 130 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 66 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 130 217 (accept_3_3 65 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 130 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 64 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 63 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 130 217 (accept_3_3 62 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 61 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 130 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 60 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 130 217 (accept_3_3 59 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 130 217 (Polychromatic418967fa.accept_17_7_11_13_1_2037 58 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 217 (accept_3_3 56 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 130 217
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 217 (accept_3_3 53 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 52 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 130 217 (accept_3_3 50 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 130 217 (Polychromatic418967fa.accept_15_4_10_7_1_1356 49 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 48 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 217 (accept_3_3 47 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 217 (Polychromatic418967fa.accept_15_1_10_7_1_4087 46 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 217 (accept_3_3 44 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 42 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 217 (accept_3_3 41 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 40 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 39 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 217 (accept_3_3 38 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 217 (Polychromatic418967fa.accept_19_18_16_8_1_12903 37 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 217
  (Polychromatic418967fa.accept_19_17_16_8_1_2099 36 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 130 217 (accept_3_3 35 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 34 130 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 217 (accept_3_3 32 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31
  130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 30 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 217 (accept_3_3 29 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 28 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 217 (accept_3_3 26 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 25 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 24 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 217 (accept_3_3 23 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 217 (Polychromatic418967fa.accept_16_6_2_9_1_5897 22 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 21 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 217 (accept_3_3 20 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 217
  (Polychromatic418967fa.accept_15_3_10_7_1_2196 18 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 217 (accept_3_3 17 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 217 (Polychromatic418967fa.accept_9_7_4_1_1_391 16 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 217 (accept_3_3 14 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 217 (Polychromatic418967fa.accept_20_13_10_17_1_5510 13 130 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 217
  (Polychromatic418967fa.accept_9_3_4_1_1_22 12 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 217 (accept_3_3 11 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 217 (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 9 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 217 (accept_3_3 8 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 217
  (Polychromatic418967fa.accept_9_6_4_1_1_390 6 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 217 (accept_3_3 5 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 217 (Polychromatic418967fa.accept_12_4_10_1_1_706 4 130 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 217 (accept_3_3 2 130 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 217 (Polychromatic418967fa.accept_15_1_10_7_1_4087 1 130 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 129 217
  (Eq.refl Bool.true) (allA_succ_of_accept 88 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 88 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 87 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 86 129 217 (accept_3_3 86 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  85 129 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 85 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 84 129 217 (Polychromatic418967fa.accept_18_12_3_1_1_3685 84 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 217 (accept_3_3 83 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 82 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 217
  (Polychromatic418967fa.accept_13_3_12_9_1_1193 81 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 129 217 (accept_3_3 80 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 129 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 79 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 129 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 78 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 217 (accept_3_3 77 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 76 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 75 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 129 217 (accept_3_3 74 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 129 217 (Polychromatic418967fa.accept_13_8_12_9_1_1168 73 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 129 217 (Polychromatic418967fa.accept_10_2_9_7_1_720 72 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 217 (accept_3_3 71 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 70 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 69 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 129 217 (accept_3_3 68 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 129 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 67 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 129 217 (Polychromatic418967fa.accept_14_10_3_7_1_1975 66 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 217 (accept_3_3 65 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 64 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 63 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 129 217 (accept_3_3 62 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 129 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 61 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 129 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 60 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 217 (accept_3_3 59 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 58 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 217
  (Polychromatic418967fa.accept_21_15_3_7_1_6748 57 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 129 217 (accept_3_3 56 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 129 217 (Polychromatic418967fa.accept_13_3_12_9_1_1193 55 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 129 217 (Polychromatic418967fa.accept_17_3_10_13_1_2021 54 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 217 (accept_3_3 53 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 52 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 51 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 129 217 (accept_3_3 50 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 129 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 49 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 129 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 48 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 217 (accept_3_3 47 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 46 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 217
  (Polychromatic418967fa.accept_16_13_1_9_1_2597 45 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 129 217 (accept_3_3 44 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 129 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 43 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 129 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 42 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 217 (accept_3_3 41 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 40 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 39 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 129 217 (accept_3_3 38 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 129 217 (Polychromatic418967fa.accept_16_5_1_9_1_4621 37 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 129 217 (Polychromatic418967fa.accept_13_10_12_9_1_1837 36 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 217 (accept_3_3 35 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 34 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 33 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 129 217 (accept_3_3 32 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 129 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 31 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 129 217 (Polychromatic418967fa.accept_18_12_3_1_1_3685 30 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 217 (accept_3_3 29 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 28 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 27 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 129 217 (accept_3_3 26 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 129 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 25 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 129 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 24 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 217 (accept_3_3 23 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 22 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 217
  (Polychromatic418967fa.accept_13_8_12_9_1_1168 21 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 129 217 (accept_3_3 20 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 129 217 (Polychromatic418967fa.accept_23_19_14_10_1_12916 19 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 217 (Polychromatic418967fa.accept_10_8_9_7_1_1118 18 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 217 (accept_3_3 17 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 16 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 217
  (Polychromatic418967fa.accept_9_6_3_1_1_155 15 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 129 217 (accept_3_3 14 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 129 217 (Polychromatic418967fa.accept_9_4_3_1_1_154 13 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 129 217 (Polychromatic418967fa.accept_10_2_9_7_1_720 12 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 217 (accept_3_3 11 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 10 129 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 217
  (Polychromatic418967fa.accept_17_9_10_13_1_6698 9 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 129 217 (accept_3_3 8 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  129 217 (Polychromatic418967fa.accept_9_7_3_1_1_386 7 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 129 217 (Polychromatic418967fa.accept_9_6_3_1_1_155 6 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 217 (accept_3_3 5 129 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 217 (Polychromatic418967fa.accept_6_4_3_1_1_57 4 129 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 217
  (Polychromatic418967fa.accept_12_3_9_1_1_290 3 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 129 217 (accept_3_3 2 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  129 217 (Polychromatic418967fa.accept_15_1_9_7_1_3130 1 129 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 129 217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 90 128 217 (Eq.refl Bool.true) (allA_of_3_1 90 128 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 91 127 217 (Eq.refl Bool.true) (allA_succ_of_accept 90 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2
  90 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 127 217 (accept_3_3 89
  127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 127 217
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 88 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 127 217 (Polychromatic418967fa.accept_21_3_1_7_1_5187 87 127 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 127 217 (accept_3_3 86 127 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 127 217 (Polychromatic418967fa.accept_24_13_7_1_1_7774 85 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 127 217
  (Polychromatic418967fa.accept_13_6_10_9_1_4329 84 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 127 217 (accept_3_3 83 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 82 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 127 217 (Polychromatic418967fa.accept_19_5_13_8_1_3229 81 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 127 217 (accept_3_3 80 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 127 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 79 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 78 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 127 217 (accept_3_3 77 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 127 217 (Polychromatic418967fa.accept_14_6_1_7_1_2775 76 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 127 217 (Polychromatic418967fa.accept_19_18_13_8_1_10099 75 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 127 217 (accept_3_3 74 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 127 217 (Polychromatic418967fa.accept_17_5_8_13_1_7994 73 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 127 217
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 72 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 127 217 (accept_3_3 71 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 70 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 127 217 (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 127 217 (accept_3_3 68 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 127 217 (Polychromatic418967fa.accept_21_4_1_7_1_3771 67 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 66 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 127 217 (accept_3_3 65 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 217 (Polychromatic418967fa.accept_13_12_10_9_1_1166 64 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 217 (Polychromatic418967fa.accept_19_6_13_8_1_4508 63 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 217 (accept_3_3 62 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 217 (Polychromatic418967fa.accept_19_4_13_8_1_11544 61 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 217
  (Polychromatic418967fa.accept_19_3_13_8_1_4476 60 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 217 (accept_3_3 59 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 58 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 217 (Polychromatic418967fa.accept_21_15_1_7_1_6723 57 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 217 (accept_3_3 56 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 217 (Polychromatic418967fa.accept_14_13_1_7_1_1211 55 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 54 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 217 (accept_3_3 53 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 217 (Polychromatic418967fa.accept_19_14_13_8_1_5943 52 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 217 (Polychromatic418967fa.accept_13_12_10_9_1_1166 51 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 217 (accept_3_3 50 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 217 (Polychromatic418967fa.accept_17_15_8_13_1_6628 49 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 217
  (Polychromatic418967fa.accept_14_6_1_7_1_2775 48 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 217 (accept_3_3 47 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 46 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 217 (Polychromatic418967fa.accept_13_6_10_9_1_4329 45 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 217 (accept_3_3 44 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 217 (Polychromatic418967fa.accept_19_5_13_8_1_3229 43 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 42 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 217 (accept_3_3 41 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 40 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 217 (Polychromatic418967fa.accept_17_5_8_13_1_7994 39 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 217 (accept_3_3 38 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 217 (Polychromatic418967fa.accept_17_3_8_13_1_5361 37 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 217
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 217 (accept_3_3 35 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 34 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 217 (Polychromatic418967fa.accept_19_14_13_8_1_5943 33 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 217 (accept_3_3 32 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 217 (Polychromatic418967fa.accept_21_10_1_7_1_12915 31 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 30 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 217 (accept_3_3 29 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 217 (Polychromatic418967fa.accept_20_8_7_17_1_8576 28 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 27 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 217 (accept_3_3 26 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 217 (Polychromatic418967fa.accept_11_3_6_8_1_1924 25 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 217
  (Polychromatic418967fa.accept_16_8_15_9_1_4676 24 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 217 (accept_3_3 23 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 217 (Polychromatic418967fa.accept_17_4_8_13_1_7960 21 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 217 (accept_3_3 20 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 217 (Polychromatic418967fa.accept_13_6_10_9_1_4329 19 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 217
  (Polychromatic418967fa.accept_4_2_3_1_1_2 18 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 217 (accept_3_3 17 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 217 (Polychromatic418967fa.accept_20_16_7_17_1_5459 16 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 217 (Polychromatic418967fa.accept_17_15_8_13_1_6628 15 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 217 (accept_3_3 14 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 217 (Polychromatic418967fa.accept_14_13_1_7_1_1211 13 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 217
  (Polychromatic418967fa.accept_13_12_10_9_1_1166 12 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 127 217 (accept_3_3 11 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 127 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 217 (Polychromatic418967fa.accept_20_9_7_17_1_1655 9 127
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 217 (accept_3_3 8 127 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 217
  (Polychromatic418967fa.accept_22_7_17_19_1_11296 7 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 217 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 127 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 217 (accept_3_3 5 127 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 217 (Polychromatic418967fa.accept_17_4_8_13_1_7960 4 127 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 217
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 217 (accept_3_3 2 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 217 (Polychromatic418967fa.accept_13_1_10_9_1_215 1 127 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127
  217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 126 217
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 126 217 7 13 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 90 126 217 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 126 217 (accept_3_3 89 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 217
  (Polychromatic418967fa.accept_15_13_6_7_1_1369 88 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 87 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 217 (accept_3_3 86 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 126 217 (Polychromatic418967fa.accept_16_5_14_9_1_2572 85 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 126 217 7 12 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 126 217 (accept_3_3 83 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 217
  (Polychromatic418967fa.accept_19_6_12_8_1_8798 82 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 126 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 81 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 217 (accept_3_3 80 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 79 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 126 217
  (Polychromatic418967fa.accept_22_12_16_19_1_12914 78 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 77 126 217 7 11 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 76 126 217 (Polychromatic418967fa.accept_15_1_6_7_1_6282 76 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 75 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 126 217 (accept_3_3 74 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 126 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 73 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 126 217 (Polychromatic418967fa.accept_15_12_6_7_1_1353 72 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 126 217 (accept_3_3 71 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 217 7 10 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 217 (Polychromatic418967fa.accept_11_3_5_8_1_458
  69 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 217 (accept_3_3 68
  126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 67 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 126 217 (Polychromatic418967fa.accept_23_20_11_10_1_12913 66 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 126 217 (accept_3_3 65 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 217 (Polychromatic418967fa.accept_19_7_12_8_1_10122 64 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 126 217 7 9 18 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 126 217 (accept_3_3 62
  126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 126 217
  (Polychromatic418967fa.accept_10_1_6_7_1_710 61 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 126 217 (Polychromatic418967fa.accept_24_12_6_1_1_11195 60 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 217 (accept_3_3 59 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 58 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 217
  (Polychromatic418967fa.accept_11_2_5_8_1_470 57 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 217 7 8 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 55 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 126 217 (Polychromatic418967fa.accept_28_26_14_21_1_8894 54
  126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 126 217 (accept_3_3 53
  126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 217
  (Polychromatic418967fa.accept_16_4_14_9_1_4657 52 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 51 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 217 (accept_3_3 50 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 49 126 217 7 7 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 48 126 217 (Polychromatic418967fa.accept_19_10_12_8_1_10124 48 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 126 217 (accept_3_3 47 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 217 (Polychromatic418967fa.accept_11_2_5_8_1_470
  46 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 217
  (Polychromatic418967fa.accept_17_11_7_13_1_11667 45 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 126 217 (accept_3_3 44 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 43 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 217 7 6 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 217 (accept_3_3 41 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 217 (Polychromatic418967fa.accept_17_6_7_13_1_3062 40 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 217
  (Polychromatic418967fa.accept_4_3_2_1_1_50 39 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 126 217 (accept_3_3 38 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 126 217 (Polychromatic418967fa.accept_16_5_14_9_1_2572 37 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 126 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 126 217 7 5 18 31 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 126 217
  (Polychromatic418967fa.accept_19_15_12_8_1_5922 34 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 126 217 (Polychromatic418967fa.accept_10_3_6_7_1_2188 33 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 217 (accept_3_3 32 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 31 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 126 217
  (Polychromatic418967fa.accept_19_11_12_8_1_11492 30 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 217 (accept_3_3 29 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 217 7 4 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 27 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 217 (accept_3_3 26 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 126 217 (Polychromatic418967fa.accept_11_3_5_8_1_458 25 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 126 217
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 126 217 (accept_3_3 23 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 126 217 (Polychromatic418967fa.accept_23_22_11_10_1_6063 22 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 217 7 3 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 217 (accept_3_3 20 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 126 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 126 217
  (Polychromatic418967fa.accept_24_18_6_1_1_11229 18 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 217 (accept_3_3 17 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 126 217 (Polychromatic418967fa.accept_15_1_6_7_1_6282 16 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 217 7 2 18 31 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 217
  (Polychromatic418967fa.accept_10_3_6_7_1_2188 13 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 126 217 (Polychromatic418967fa.accept_15_12_6_7_1_1353 12 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 126 217 (accept_3_3 11 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 126 217 (Polychromatic418967fa.accept_19_10_12_8_1_10124 10 126 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 217
  (Polychromatic418967fa.accept_20_9_6_17_1_1654 9 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 126 217 (accept_3_3 8 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 126
  217 7 1 18 31 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6
  126 217 (Polychromatic418967fa.accept_17_6_7_13_1_3062 6 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 217 (accept_3_3 5 126 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 217 (Polychromatic418967fa.accept_16_4_14_9_1_4657 4 126 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 217 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 217 (accept_3_3 2 126 217
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 217 (Polychromatic418967fa.accept_10_1_6_7_1_710 1
  126 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  217)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 125 217
  (Eq.refl Bool.true) (allA_of_3_1 93 125 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 94 124 217 (Eq.refl
  Bool.true) (allA_succ_of_gcd 93 124 217 31 3 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 92 124 217 (accept_3_3 92 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 124 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 91 124 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 124 217 (Polychromatic418967fa.accept_22_2_14_19_1_11310 90
  124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 124 217 (accept_3_3 89
  124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 124 217
  (Polychromatic418967fa.accept_16_8_12_9_1_2569 88 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 87 124 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 124 217 (accept_3_3 86 124 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 124 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 85 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 124 217 (Polychromatic418967fa.accept_9_3_7_1_1_143
  84 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 124 217 (accept_3_3 83
  124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 124 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 82 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 81 124 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 124 217 (accept_3_3 80 124 217 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 124 217 (Polychromatic418967fa.accept_14_9_12_7_1_597 79 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 124 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 78 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 124 217 (accept_3_3 77 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 76 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 75 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 124 217 (accept_3_3 74 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 124 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 73 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 124 217
  (Polychromatic418967fa.accept_10_2_4_7_1_352 72 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 124 217 (accept_3_3 71 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 124 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 70 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 69 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 124 217 (accept_3_3 68 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 67 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 124 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 66 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 124 217 (accept_3_3 65 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 217 (Polychromatic418967fa.accept_18_10_16_1_1_1534 64 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 63 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 217 31 2 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 61
  124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 60 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 124 217 (accept_3_3 59 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 58 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 57 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 217 (accept_3_3 56 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 217 (Polychromatic418967fa.accept_13_3_7_9_1_1153 55 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 217
  (Polychromatic418967fa.accept_13_2_7_9_1_2616 54 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 217 (accept_3_3 53 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 217 (Polychromatic418967fa.accept_10_2_4_7_1_352 52 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 51 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 217 (accept_3_3 50 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 49 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 217
  (Polychromatic418967fa.accept_9_3_7_1_1_143 48 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 124 217 (accept_3_3 47 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 124 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 46 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 45 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 217 (accept_3_3 44 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 217 (Polychromatic418967fa.accept_10_3_4_7_1_353 43 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 124 217
  (Polychromatic418967fa.accept_9_6_7_1_1_145 42 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 124 217 (accept_3_3 41 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 40 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 39 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 217 (accept_3_3 38 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 37 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 124 217
  (Polychromatic418967fa.accept_16_4_12_9_1_2567 36 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 124 217 (accept_3_3 35 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 34 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 217 (Polychromatic418967fa.accept_6_3_4_1_1_8 33 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 217 (accept_3_3 32 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 31 124 217 31 1 4 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 30 124 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 30 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 217 (accept_3_3 29 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 217 (Polychromatic418967fa.accept_11_6_3_8_1_843 28 124
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 27 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 217 (accept_3_3 26 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 217 (Polychromatic418967fa.accept_15_10_4_7_1_3127 25 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 24 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 217 (accept_3_3 23 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 22 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 21 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 217 (accept_3_3 20 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 217 (Polychromatic418967fa.accept_13_6_7_9_1_1848 19 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 217 (Polychromatic418967fa.accept_15_3_4_7_1_1352 18 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 217 (accept_3_3 17 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 217 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 124
  217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 15 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 217 (accept_3_3 14 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 217 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 217 (Polychromatic418967fa.accept_9_3_7_1_1_143 12 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 217 (accept_3_3 11 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 217 (Polychromatic418967fa.accept_12_10_4_1_1_1843 10 124 217
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 9 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 217 (accept_3_3 8 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 217 (Polychromatic418967fa.accept_18_7_16_1_1_4951 7 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 217 (Polychromatic418967fa.accept_9_6_7_1_1_145 6 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 217 (accept_3_3 5 124 217 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 217 (Polychromatic418967fa.accept_9_4_7_1_1_379 4 124 217 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 217
  (Polychromatic418967fa.accept_6_3_4_1_1_8 3 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 217 (accept_3_3 2 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 217 (Polychromatic418967fa.accept_10_1_4_7_1_374 1 124 217 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124
  217))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_217_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


