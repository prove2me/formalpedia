-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch215
-- name    : Polychromatic418967fa_Branch215
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:51.858986+00:00
-- url     : https://prove2.me/theorems/72b56402-d4a0-4daf-97a4-a24b3ad0d399
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch215_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_215 : allB 215 215 :=
  allB_succ' 2 214 215 (Eq.refl Bool.true) (allA_of_3_0 2 214 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  213 215 (Eq.refl Bool.true) (allA_succ_of_accept 2 213 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 213 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 215 (accept_3_2 1 213 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 213 215))) (allB_succ' 4 212 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 3 212 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 212 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 212 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 212 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 212 215 (accept_3_2 1 212 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 212 215)))) (allB_succ' 5 211 215 (Eq.refl Bool.true) (allA_of_3_0
  5 211 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 6 210 215 (Eq.refl Bool.true) (allA_succ_of_gcd 5 210
  215 5 1 42 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4
  210 215 (accept_3_2 4 210 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 210 215
  (Polychromatic418967fa.accept_19_3_1_6_1_3114 3 210 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 210 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 210 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 210 215 (accept_3_2 1 210 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 210 215)))))) (allB_succ' 7 209 215 (Eq.refl Bool.true) (allA_succ_of_accept 6 209 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 209 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 209 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 209 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 209 215 (accept_3_2 4 209 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 209 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 209 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 209 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2
  209 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 215 (accept_3_2 1 209
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 209 215))))))) (allB_succ' 8 208 215 (Eq.refl Bool.true)
  (allA_of_3_0 8 208 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 207 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 8 207 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 207 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 215 (accept_3_2 7 207 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 207 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 207 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 215 (Polychromatic418967fa.accept_13_5_12_7_1_1080
  5 207 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 207 215 (accept_3_2 4
  207 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 207 215
  (Polychromatic418967fa.accept_10_3_7_5_1_288 3 207 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 207 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 207 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 215 (accept_3_2 1 207 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 207 215))))))))) (allB_succ' 10 206 215 (Eq.refl Bool.true) (allA_succ_of_accept 9 206 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 206 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 206 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 206 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 206 215 (accept_3_2 7 206 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 206 215 (Polychromatic418967fa.accept_15_6_11_5_1_168 6 206 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 206 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  206 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 206 215 (accept_3_2 4 206
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 206 215 (Polychromatic418967fa.accept_6_3_2_5_1_32
  3 206 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 206 215
  (Polychromatic418967fa.accept_7_2_3_5_1_34 2 206 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 206 215 (accept_3_2 1 206 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  215)))))))))) (allB_succ' 11 205 215 (Eq.refl Bool.true) (allA_of_3_0 11 205 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 204 215 (Eq.refl Bool.true) (allA_succ_of_accept 11 204 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 204 215 (accept_3_2 10 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  204 215 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 204 215 (Polychromatic418967fa.accept_13_8_9_7_1_530 8 204 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 204 215 (accept_3_2 7 204 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 204 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 204 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 204 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 204 215 (accept_3_2 4 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  204 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 204 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 204 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 204 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 204 215 (accept_3_2 1 204 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 204 215)))))))))))) (allB_succ' 13 203 215 (Eq.refl Bool.true) (allA_succ_of_accept 12
  203 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 203 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 203 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 215 (accept_3_2 10 203 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 203 215 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 203 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 215
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 203 215 (accept_3_2 7 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  203 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 203 215 (Polychromatic418967fa.accept_16_5_11_7_1_5635 5 203 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 215 (accept_3_2 4 203 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 203 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 203 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 215 (accept_3_2 1 203 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  215))))))))))))) (allB_succ' 14 202 215 (Eq.refl Bool.true) (allA_of_3_0 14 202 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 201 215 (Eq.refl Bool.true) (allA_succ_of_accept 14 201 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 201 215 (accept_3_2 13 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 201 215 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 201 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 201 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 215 (accept_3_2 10 201 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 201 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 201 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 215 (accept_3_2 7 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  201 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 201 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 201 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 215 (accept_3_2 4 201 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 201 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 201 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 201 215 (accept_3_2 1 201 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201
  215))))))))))))))) (allB_succ' 16 200 215 (Eq.refl Bool.true) (allA_succ_of_gcd 15 200 215 5 3 40 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 200 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 200 215 (accept_3_2 13 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 200 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 200 215 (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 200 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 215 5 2 40 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 200 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 200 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 200 215 (accept_3_2 7 200 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 200 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 200 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 200 215 5 1 40 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 200 215 (accept_3_2 4 200 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 200 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 200 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 200 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 200 215 (accept_3_2 1 200 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  215)))))))))))))))) (allB_succ' 17 199 215 (Eq.refl Bool.true) (allA_of_3_0 17 199 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 198 215 (Eq.refl Bool.true) (allA_succ_of_accept 17 198 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 198 215 (accept_3_2 16 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 198 215 (Polychromatic418967fa.accept_16_15_6_7_1_4512 15 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 198 215 (Polychromatic418967fa.accept_13_1_3_7_1_1710 14 198 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 198 215 (accept_3_2 13 198 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 198 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 198
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 198 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 198 215 (accept_3_2 10 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  198 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 198 215 (Polychromatic418967fa.accept_13_8_3_7_1_2455 8 198 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 198 215 (accept_3_2 7 198 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 198 215 (Polychromatic418967fa.accept_15_6_3_5_1_607 6 198 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 198 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 198 215 (accept_3_2 4 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  198 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 198 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 198 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 198 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 198 215 (accept_3_2 1 198 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198 215)))))))))))))))))) (allB_succ' 19 197 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 18 197 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 197 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 197 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 197 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 215 (accept_3_2 16 197 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 197 215
  (Polychromatic418967fa.accept_21_15_8_5_1_12668 15 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 197 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 215 (accept_3_2 13 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 215 (Polychromatic418967fa.accept_10_2_7_5_1_605 12 197 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 215 (accept_3_2 10 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 215 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 215 (Polychromatic418967fa.accept_10_8_7_5_1_602 8 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 215 (accept_3_2 7 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 197 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 215
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 215 (accept_3_2 4 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 197 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 215 (accept_3_2 1 197 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 215))))))))))))))))))) (allB_succ' 20 196 215 (Eq.refl Bool.true) (allA_of_3_0 20
  196 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 195 215 (Eq.refl Bool.true) (allA_succ_of_gcd 20 195
  215 5 4 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19
  195 215 (accept_3_2 19 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 195 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 18 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 195 215 (Polychromatic418967fa.accept_25_17_20_15_1_7240 17 195 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 215 (accept_3_2 16 195 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 195 215 5 3 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 195 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 195 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 215 (accept_3_2 13 195 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 195 215 (Polychromatic418967fa.accept_8_4_3_7_1_491
  12 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 195 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 195 215 5 2 39 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 195 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 195 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 195 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 215 (accept_3_2 7 195 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 195 215 (Polychromatic418967fa.accept_14_6_13_5_1_534
  6 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 195 215 5 1 39 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 215 (accept_3_2 4
  195 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 215
  (Polychromatic418967fa.accept_9_3_6_8_1_308 3 195 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 195 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 195 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 215 (accept_3_2 1 195 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 195 215))))))))))))))))))))) (allB_succ' 22 194 215 (Eq.refl Bool.true) (allA_succ_of_accept 21
  194 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 194 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 194 215 (accept_3_2 19 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 194 215 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 194 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 194 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 194 215 (accept_3_2 16 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 194 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 194 215 (Polychromatic418967fa.accept_27_14_5_26_1_12700 14 194 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 194 215 (accept_3_2 13 194 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 194 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 194 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 194 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 194 215 (accept_3_2 10 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  194 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 194 215 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 194 215 (accept_3_2 7 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 194 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 194 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 194 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 194 215 (accept_3_2 4 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  194 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 194 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 194 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 194 215 (accept_3_2 1 194 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 215)))))))))))))))))))))) (allB_succ' 23 193 215 (Eq.refl Bool.true) (allA_of_3_0
  23 193 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 192 215 (Eq.refl Bool.true) (allA_succ_of_accept 23
  192 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 192 215 (accept_3_2 22 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 192 215 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 192 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 192 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 192 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 192 215 (accept_3_2 19 192 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 192 215 (Polychromatic418967fa.accept_10_8_2_5_1_596
  18 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 192 215
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 192 215 (accept_3_2 16 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 192 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 192 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 192 215 (accept_3_2 13 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 192 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 192 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 192 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 192 215 (accept_3_2 10 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  192 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 192 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 215 (accept_3_2 7 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 192 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 192 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 192 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 215 (accept_3_2 4 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  192 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 3 192 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 192 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 215 (accept_3_2 1 192 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 192 215)))))))))))))))))))))))) (allB_succ' 25 191 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 24 191 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 191 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 191 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 191 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 215 (accept_3_2 22 191 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 215 (Polychromatic418967fa.accept_9_3_2_8_1_108
  21 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 215
  (Polychromatic418967fa.accept_18_2_11_17_1_4773 20 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 191 215 (accept_3_2 19 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 191 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 191 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 191 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 191 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 215 (accept_3_2 16 191 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 215 (Polychromatic418967fa.accept_9_6_2_8_1_592
  15 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 215 (accept_3_2 13 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 191 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 215 (accept_3_2 10 191 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 191 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 215
  (Polychromatic418967fa.accept_13_8_9_7_1_530 8 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 215 (accept_3_2 7 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 191 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 215 (accept_3_2 4 191 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 191 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 215
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 215 (accept_3_2 1 191 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  215))))))))))))))))))))))))) (allB_succ' 26 190 215 (Eq.refl Bool.true) (allA_of_3_0 26 190 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 27 189 215 (Eq.refl Bool.true) (allA_succ_of_accept 26 189 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 189 215 (accept_3_2 25 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 189 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 189 215 (Polychromatic418967fa.accept_14_9_7_5_1_1105 23 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 189 215 (accept_3_2 22 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 189 215 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 189 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 189 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 215 (accept_3_2 19 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 189 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 189 215 (Polychromatic418967fa.accept_19_17_18_6_1_7192 17 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 189 215 (accept_3_2 16 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 189 215 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 189
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 189 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 189 215 (accept_3_2 13 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 189 215 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 189 215 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 189 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 215 (accept_3_2 10 189 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 189 215 (Polychromatic418967fa.accept_14_9_7_5_1_1105 9 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 189 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 215 (accept_3_2 7 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  189 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 189 215 (Polychromatic418967fa.accept_19_5_18_6_1_7191 5 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 215 (accept_3_2 4 189 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 189 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 189 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 189 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 215 (accept_3_2 1 189 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189
  215))))))))))))))))))))))))))) (allB_succ' 28 188 215 (Eq.refl Bool.true) (allA_succ_of_accept 27 188 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 188 215 (Polychromatic418967fa.accept_12_2_8_11_1_31 26 188 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 188 215 (accept_3_2 25 188 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 188 215 (Polychromatic418967fa.accept_16_8_12_7_1_2399 24 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 188 215
  (Polychromatic418967fa.accept_10_3_8_5_1_606 23 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 188 215 (accept_3_2 22 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 188 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 188 215 (Polychromatic418967fa.accept_16_4_12_7_1_4475 20 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 188 215 (accept_3_2 19 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 188 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 188 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 188 215
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 188 215 (accept_3_2 16 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 188 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 188 215 (Polychromatic418967fa.accept_12_2_8_11_1_31 14 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 188 215 (accept_3_2 13 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 188 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 188
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 188 215 (accept_3_2 10 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  188 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 188 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 188 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 188 215 (accept_3_2 7 188 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 188 215 (Polychromatic418967fa.accept_21_6_20_5_1_12663 6 188 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 188 215
  (Polychromatic418967fa.accept_11_5_1_6_1_774 5 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 188 215 (accept_3_2 4 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  188 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 188 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 188 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 188 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 188 215 (accept_3_2 1 188 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 188 215)))))))))))))))))))))))))))) (allB_succ' 29 187 215 (Eq.refl Bool.true)
  (allA_of_3_0 29 187 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 186 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 186 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 186 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 186 215 (accept_3_2 28 186 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 186 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 186 215
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 186 215 (accept_3_2 25 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 186 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 186 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 186 215 (accept_3_2 22 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 186 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 186 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 186 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 186 215 (accept_3_2 19 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 186 215 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 186 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 186 215 (accept_3_2 16 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 186 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 186 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 186 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 186 215 (accept_3_2 13 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 186 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 186 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 186 215 (accept_3_2 10 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 186 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 186 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 186 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 186 215 (accept_3_2 7 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  186 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 186 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 215 (accept_3_2 4 186 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 186 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 186 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 186 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 215 (accept_3_2 1 186 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  215)))))))))))))))))))))))))))))) (allB_succ' 31 185 215 (Eq.refl Bool.true) (allA_succ_of_gcd 30 185 215 5 6 37 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 185 215
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 185 215 (accept_3_2 28 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 185 215 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 185 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 185 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 185 215 5 5 37 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 185 215
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 185 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 185 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 215 (accept_3_2 22 185 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 185 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 185 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 185 215 5 4 37 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 185 215 (accept_3_2 19 185 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 185 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 185 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 185 215
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 185 215 (accept_3_2 16 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  185 215 5 3 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 185 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 185 215 (accept_3_2 13 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 185 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 185 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 185 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 185 215 5 2 37 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 215
  (Polychromatic418967fa.accept_7_2_3_5_1_34 9 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 185 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 215 (accept_3_2 7 185 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 215 5 1 37 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 215 (accept_3_2 4 185 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 185 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 215 (accept_3_2 1 185 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  215))))))))))))))))))))))))))))))) (allB_succ' 32 184 215 (Eq.refl Bool.true) (allA_of_3_0 32 184 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 183 215 (Eq.refl Bool.true) (allA_succ_of_accept 32 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 183 215 (accept_3_2 31 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 183 215 (Polychromatic418967fa.accept_20_10_3_15_1_1546 30 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 183 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 29 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 215 (accept_3_2 28 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 183 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 183 215 (accept_3_2 25 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 183 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 183 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 215 (accept_3_2 22 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 183 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 215 (accept_3_2 19 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 183 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 183 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 215 (accept_3_2 16 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 183 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 183 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 183 215 (accept_3_2 13 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 183 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 183 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 183 215 (accept_3_2 10 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 183 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 183 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 183 215 (accept_3_2 7 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  183 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 183 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 215 (accept_3_2 4 183 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 183 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 183 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 183 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 215 (accept_3_2 1 183 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 183
  215))))))))))))))))))))))))))))))))) (allB_succ' 34 182 215 (Eq.refl Bool.true) (allA_succ_of_accept 33 182 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 182 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 182 215 (accept_3_2 31 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 182 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 182 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 182 215 (accept_3_2 28
  182 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 182 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 27 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 182 215 (Polychromatic418967fa.accept_15_11_2_5_1_2076 26 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 182 215 (accept_3_2 25 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 182 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 182 215 (Polychromatic418967fa.accept_9_5_2_8_1_109
  23 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 182 215 (accept_3_2 22
  182 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 182 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 182 215 (Polychromatic418967fa.accept_12_8_2_11_1_246 20 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 182 215 (accept_3_2 19 182 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 182 215 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 182 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 182 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 182 215 (accept_3_2 16 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 182 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 182 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 182 215 (accept_3_2 13 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 182 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 182 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 215
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 182 215 (accept_3_2 10 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  182 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 182 215 (Polychromatic418967fa.accept_10_8_2_5_1_596 8 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 215 (accept_3_2 7 182 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 182 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 182 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 182 215 (accept_3_2 4 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  182 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 182 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 182 215 (Polychromatic418967fa.accept_22_2_6_17_1_4686 2 182 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 215 (accept_3_2 1 182 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 182 215)))))))))))))))))))))))))))))))))) (allB_succ' 35 181 215 (Eq.refl
  Bool.true) (allA_of_3_0 35 181 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 180 215 (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 180 215 5 7 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 180 215 (accept_3_2 34 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 180 215 (Polychromatic418967fa.accept_19_14_9_6_1_8633 33 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 180 215 (Polychromatic418967fa.accept_19_13_9_6_1_4393 32 180 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 180 215 (accept_3_2 31 180 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 180 215 5 6 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 180 215 (Polychromatic418967fa.accept_13_3_11_7_1_2488
  29 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 180 215 (accept_3_2 28
  180 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 180 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 27 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 180 215 (Polychromatic418967fa.accept_25_1_5_15_1_12699 26 180 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 180 215 5 5 36 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 180 215
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 180 215 (Polychromatic418967fa.accept_29_23_6_12_1_12698 23 180 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 180 215 (accept_3_2 22 180 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 180 215 (Polychromatic418967fa.accept_14_7_12_5_1_1861 21 180 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 180 215 5 4 36 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 215 (accept_3_2 19
  180 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 180 215
  (Polychromatic418967fa.accept_13_5_11_7_1_559 18 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 180 215 (Polychromatic418967fa.accept_13_4_11_7_1_558 17 180 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 180 215 (accept_3_2 16 180 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 180 215 5 3 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 180 215 (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 180 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 180 215 (accept_3_2 13 180 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 180 215 (Polychromatic418967fa.accept_13_12_11_7_1_2491 12 180
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 180 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 180 215 5 2 36 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 180 215 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 180 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 180 215 (Polychromatic418967fa.accept_16_8_4_7_1_3390 8 180 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 215 (accept_3_2 7 180 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 180 215 (Polychromatic418967fa.accept_21_6_12_5_1_6593
  6 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 180 215 5 1 36 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 180 215 (accept_3_2 4
  180 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 180 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 180 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 180 215 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 180 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 215 (accept_3_2 1 180 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 215)))))))))))))))))))))))))))))))))))) (allB_succ' 37 179 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 36 179 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 215 (Polychromatic418967fa.accept_19_16_8_6_1_4407 35 179
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 215 (accept_3_2 34 179
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 215
  (Polychromatic418967fa.accept_19_14_8_6_1_981 33 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 179 215 (Polychromatic418967fa.accept_15_2_14_5_1_2072 32 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 215 (accept_3_2 31 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 179 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 29
  179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 215 (accept_3_2 28
  179 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 27 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 179 215 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 215 (accept_3_2 25 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 179 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 215 (Polychromatic418967fa.accept_7_2_4_5_1_313
  23 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 215 (accept_3_2 22
  179 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 215
  (Polychromatic418967fa.accept_10_1_9_5_1_83 21 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 179 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 215 (accept_3_2 19 179 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 179 215 (Polychromatic418967fa.accept_21_18_11_5_1_3487 18 179 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 215
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 215 (accept_3_2 16 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 215 (accept_3_2 13 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 179 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 215
  (Polychromatic418967fa.accept_10_1_9_5_1_83 11 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 215 (accept_3_2 10 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 215 (accept_3_2 7 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 179 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 215
  (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 215 (accept_3_2 4 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 215 (Polychromatic418967fa.accept_13_3_10_7_1_1061 3 179 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 2 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 215 (accept_3_2 1 179 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 215))))))))))))))))))))))))))))))))))))) (allB_succ' 38 178 215 (Eq.refl Bool.true)
  (allA_of_3_0 38 178 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 177 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 38 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 177 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 215 (accept_3_2 37 177 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 177 215 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 215
  (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 215 (accept_3_2 34 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 215 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 215 (accept_3_2 31 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 215 (accept_3_2 28 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 215 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 215 (accept_3_2 25 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 215 (accept_3_2 22 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 215 (accept_3_2 19 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 215 (accept_3_2 16 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 215 (accept_3_2 13 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 215 (accept_3_2 10 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 215 (Polychromatic418967fa.accept_13_9_8_7_1_1073 9 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 215 (accept_3_2 7 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 177 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 215 (accept_3_2 4 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 177 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 215 (accept_3_2 1 177 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 215))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 176 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 39 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 176 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 38
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 176 215 (accept_3_2 37
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 176 215
  (Polychromatic418967fa.accept_15_6_11_5_1_168 36 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 176 215 (Polychromatic418967fa.accept_21_14_8_5_1_6586 35 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 176 215 (accept_3_2 34 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 176 215 (Polychromatic418967fa.accept_7_4_1_5_1_540
  32 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 176 215 (accept_3_2 31
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 176 215
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 176 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 176 215 (accept_3_2 28 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 176 215 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 176 215 (accept_3_2 25
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 176 215
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 176 215 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 215 (accept_3_2 22 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 176 215 (Polychromatic418967fa.accept_7_6_1_5_1_322
  20 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 215 (accept_3_2 19
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 18 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 176 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 215 (accept_3_2 16 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 215 (Polychromatic418967fa.accept_10_4_6_5_1_74
  14 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 215 (accept_3_2 13
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 215
  (Polychromatic418967fa.accept_9_3_5_8_1_99 12 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 176 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 215 (accept_3_2 10 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 215 (Polychromatic418967fa.accept_15_8_11_5_1_169
  8 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 215 (accept_3_2 7
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 215
  (Polychromatic418967fa.accept_7_6_1_5_1_322 6 176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 176 215 (Polychromatic418967fa.accept_17_5_6_11_1_3974 5 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 215 (accept_3_2 4 176 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 176 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 176 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 2
  176 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 215 (accept_3_2 1 176
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 215)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41
  175 215 (Eq.refl Bool.true) (allA_of_3_0 41 175 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 174 215
  (Eq.refl Bool.true) (allA_succ_of_accept 41 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 174 215 (accept_3_2 40 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 174 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 174 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 174 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 174 215 (accept_3_2 37 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 174 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 174 215 (Polychromatic418967fa.accept_19_16_3_6_1_1941 35 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 174 215 (accept_3_2 34 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 174 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 174 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 174 215 (accept_3_2 31 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 174 215 (Polychromatic418967fa.accept_20_10_14_15_1_9885 30 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 174 215 (accept_3_2 28 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 174 215 (Polychromatic418967fa.accept_14_13_6_5_1_1853 27 174
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 174 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 174 215 (accept_3_2 25 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 174 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 174 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 174 215 (accept_3_2 22 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 174 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 174 215 (accept_3_2 19 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 174 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 174 215 (accept_3_2 16 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 174 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 174 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 174 215 (accept_3_2 13 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 174 215 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 174 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 215 (accept_3_2 10 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 174 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 215 (accept_3_2 7 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  174 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 174 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 215 (accept_3_2 4 174 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 174 215 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 174 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 174 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 174 215 (accept_3_2 1 174 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  215)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 173 215 (Eq.refl Bool.true) (allA_succ_of_accept 42 173
  215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 173 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 215 (accept_3_2 40 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 173 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 173 215 (accept_3_2 37
  173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 173 215
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 173 215 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 215 (accept_3_2 34 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 173 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 215 (Polychromatic418967fa.accept_9_5_2_8_1_109
  32 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 173 215 (accept_3_2 31
  173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 173 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 173 215 (Polychromatic418967fa.accept_13_3_4_7_1_1711 29 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 215 (accept_3_2 28 173 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 173 215 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 215 (accept_3_2 25 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 215 (accept_3_2 22 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 215
  (Polychromatic418967fa.accept_16_4_13_7_1_4522 20 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 215 (accept_3_2 19 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 215 (Polychromatic418967fa.accept_10_7_3_5_1_301 17 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 215 (accept_3_2 16 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 173 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 215 (accept_3_2 13 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 215 (Polychromatic418967fa.accept_13_11_4_7_1_2419 11 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 215 (accept_3_2 10 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 215 (Polychromatic418967fa.accept_13_9_4_7_1_1694 9 173 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 215
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 215 (accept_3_2 7 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 215 (accept_3_2 4 173 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 173 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 215 (accept_3_2 1 173 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  215))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 172 215 (Eq.refl Bool.true) (allA_of_3_0 44 172 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 171 215 (Eq.refl Bool.true) (allA_succ_of_accept 44 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 171 215 (accept_3_2 43 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 171 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 42 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 171 215 (Polychromatic418967fa.accept_15_11_6_5_1_1295 41 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 171 215 (accept_3_2 40 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 171 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 171
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 215 (accept_3_2 37 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 171 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 171 215 (Polychromatic418967fa.accept_13_9_2_7_1_1083 35 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 171 215 (accept_3_2 34 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 171 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 171
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 215 (accept_3_2 31 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 171 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 171 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 171 215 (accept_3_2 28 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 171 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 171 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 26 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 171 215 (accept_3_2 25 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 171 215 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 171 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 215 (accept_3_2 22 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 171 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 171 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 215 (accept_3_2 19 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 171 215 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 171 215 (Polychromatic418967fa.accept_25_17_21_15_1_12652 17 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 215 (accept_3_2 16 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 171 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 171 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 14 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 215 (accept_3_2 13 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 171 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 171 215 (Polychromatic418967fa.accept_15_11_6_5_1_1295 11 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 215 (accept_3_2 10 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 171 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 171 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 215 (accept_3_2 7 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  171 215 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 171 215 (Polychromatic418967fa.accept_13_5_2_7_1_2414 5 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 215 (accept_3_2 4 171 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 171 215 (Polychromatic418967fa.accept_15_3_6_5_1_2079 3 171 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 215 (accept_3_2 1 171 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171
  215))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 170 215 (Eq.refl Bool.true) (allA_succ_of_gcd 45 170
  215 5 9 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  170 215 (Polychromatic418967fa.accept_12_8_2_11_1_246 44 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 170 215 (accept_3_2 43 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 170 215 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 170 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 170 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 215 5 8 34 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 170 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 170 215 (accept_3_2 37 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 170 215 (Polychromatic418967fa.accept_19_17_18_6_1_7192 36 170 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 170 215 5 7 34 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 170 215 (accept_3_2 34 170 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 170 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 170 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 170 215 (accept_3_2 31 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  170 215 5 6 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 170 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 170 215 (accept_3_2 28 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 170 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 170 215 (Polychromatic418967fa.accept_19_7_18_6_1_3095 26 170
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 170 215 5 5 34 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 170 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 170 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 215 (accept_3_2 22 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 170 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 170 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 215 5 4 34 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 215 (accept_3_2 19 170 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 170 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 170 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 170 215 (accept_3_2 16 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  170 215 5 3 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 170 215 (Polychromatic418967fa.accept_16_14_10_7_1_2363 14 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 170 215 (accept_3_2 13 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 170 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 170 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 215 5 2 34 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 215
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 170 215 (Polychromatic418967fa.accept_12_8_2_11_1_246 8 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 215 (accept_3_2 7 170 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 170 215 (Polychromatic418967fa.accept_13_6_1_7_1_1690 6 170 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 170 215 5 1 34 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 170 215 (accept_3_2 4 170 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 170 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 215
  (Polychromatic418967fa.accept_18_2_8_17_1_4754 2 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 215 (accept_3_2 1 170 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  215)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 169 215 (Eq.refl Bool.true) (allA_of_3_0 47 169 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 168 215 (Eq.refl Bool.true) (allA_succ_of_accept 47 168 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 168 215 (accept_3_2 46 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 168 215 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 168 215 (Polychromatic418967fa.accept_13_5_12_7_1_1080 44 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 168 215 (accept_3_2 43 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 168 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 168
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 168 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 168 215 (accept_3_2 40 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 168 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 168 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 168 215 (accept_3_2 37 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 168 215 (Polychromatic418967fa.accept_13_10_12_7_1_1079 36 168 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 168 215
  (Polychromatic418967fa.accept_29_6_23_12_1_12697 35 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 168 215 (accept_3_2 34 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 168 215 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 168 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 168 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 168 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 168 215 (accept_3_2 31 168 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 168 215 (Polychromatic418967fa.accept_9_3_6_8_1_308
  30 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 168 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 168 215 (accept_3_2 28 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 168 215 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 168 215 (Polychromatic418967fa.accept_19_7_16_6_1_4400 26 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 215 (accept_3_2 25 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 168 215 (Polychromatic418967fa.accept_13_11_12_7_1_2443 24 168
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 168 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 168 215 (accept_3_2 22 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 168 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 168 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 168 215 (accept_3_2 19 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 168 215 (Polychromatic418967fa.accept_13_5_12_7_1_1080 18 168 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 168 215
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 215 (accept_3_2 16 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 168 215 (Polychromatic418967fa.accept_16_15_8_7_1_3407 15 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 168 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 215 (accept_3_2 13 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 168 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 168 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 215 (accept_3_2 10 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  168 215 (Polychromatic418967fa.accept_11_9_3_6_1_797 9 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 168 215 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 215 (accept_3_2 7 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 168 215 (Polychromatic418967fa.accept_13_6_12_7_1_5131 6 168 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 168 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 168 215 (accept_3_2 4 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  168 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 168 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 168 215 (accept_3_2 1 168 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 215)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 167 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 48 167 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 47
  167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 215 (accept_3_2 46
  167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 215
  (Polychromatic418967fa.accept_20_5_7_15_1_2668 45 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 167 215 (Polychromatic418967fa.accept_13_5_11_7_1_559 44 167 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 215 (accept_3_2 43 167 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 167 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 215
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 41 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 167 215 (accept_3_2 40 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 167 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 167 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 215 (accept_3_2 37 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 215
  (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 167 215 (accept_3_2 34 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 167 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 167 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 32 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 167 215 (accept_3_2 31 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 167 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 167 215 (accept_3_2 28 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 167 215 (Polychromatic418967fa.accept_13_1_11_7_1_1704 27 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 167 215 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 215 (accept_3_2 25 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 167 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 215
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 167 215 (accept_3_2 22 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 167 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 167 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 215 (accept_3_2 19 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 215
  (Polychromatic418967fa.accept_13_4_11_7_1_558 17 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 215 (accept_3_2 16 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 215 (Polychromatic418967fa.accept_13_1_11_7_1_1704 14 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 215 (accept_3_2 13 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 215 (accept_3_2 10 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 215 (Polychromatic418967fa.accept_13_9_11_7_1_1077 9 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 8 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 215 (accept_3_2 7 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 215
  (Polychromatic418967fa.accept_13_5_11_7_1_559 5 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 215 (accept_3_2 4 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 167 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 215 (accept_3_2 1 167 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 215))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 166 215
  (Eq.refl Bool.true) (allA_of_3_0 50 166 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 165 215 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 165 215 5 10 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 165 215 (accept_3_2 49 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 165 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 165 215 (accept_3_2 46 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 165 215 5 9 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 215 (accept_3_2 43 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 165 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 165 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 215 5 8 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 165 215
  (Polychromatic418967fa.accept_12_3_9_11_1_231 39 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 215 (accept_3_2 37 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 165 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 165 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 165 215 5 7 33 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 215 (accept_3_2 34 165 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 165 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 165 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 215 (accept_3_2 31 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  165 215 5 6 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 165 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 165 215 (accept_3_2 28 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 165 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 215 5 5 33 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 165 215
  (Polychromatic418967fa.accept_9_6_3_8_1_595 24 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 165 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 215 (accept_3_2 22 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 165 215 (Polychromatic418967fa.accept_13_8_9_7_1_530 21 165 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 165 215 5 4 33 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 165 215 (accept_3_2 19 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18
  165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 215
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 17 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 215 (accept_3_2 16 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  165 215 5 3 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 165 215 (accept_3_2 13 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 165 215 (Polychromatic418967fa.accept_16_12_5_7_1_2360 12 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 165 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 215 5 2 33 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 165 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 9 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 165 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 215 (accept_3_2 7 165 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 165 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 165 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 165 215 5 1 33 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 215 (accept_3_2 4 165 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 165 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 165 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 215 (accept_3_2 1 165 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165
  215))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 164 215 (Eq.refl Bool.true) (allA_succ_of_accept
  51 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 164 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 164 215 (accept_3_2 49 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 164 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 164 215
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 164 215 (accept_3_2 46 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 164 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 164 215 (accept_3_2 43 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 164 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 164 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 41 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 164 215 (accept_3_2 40 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 164 215 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 164 215 (accept_3_2 37 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 164 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 164 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 164 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 164 215 (accept_3_2 34 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 164 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 164 215 (accept_3_2 31 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 215
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 215 (accept_3_2 28 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 215 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 215 (accept_3_2 25 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 164 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 215
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 215 (accept_3_2 22 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 215 (Polychromatic418967fa.accept_22_20_10_17_1_9639 20 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 215 (accept_3_2 19 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 215 (Polychromatic418967fa.accept_19_18_12_6_1_7187 18 164
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 215
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 17 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 215 (accept_3_2 16 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 215 (accept_3_2 13 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 215 (accept_3_2 10 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 215 (accept_3_2 7 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 164 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 215 (accept_3_2 4 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 164 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 215 (accept_3_2 1 164 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 215)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 163 215
  (Eq.refl Bool.true) (allA_of_3_0 53 163 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 162 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 162 215 (accept_3_2 52 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 162 215 (Polychromatic418967fa.accept_13_12_6_7_1_1071 51 162 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 162 215
  (Polychromatic418967fa.accept_19_12_10_6_1_8668 50 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 162 215 (accept_3_2 49 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 162 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 162 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 162 215 (Polychromatic418967fa.accept_10_7_2_5_1_298 47 162
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 162 215 (accept_3_2 46 162
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9
  45 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 162 215
  (Polychromatic418967fa.accept_16_12_2_7_1_6853 44 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 162 215 (accept_3_2 43 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 162 215 (Polychromatic418967fa.accept_17_8_9_11_1_3976 42 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 162 215 (accept_3_2 40 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 162 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 162 215
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 162 215 (accept_3_2 37 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 162 215 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 162 215 (Polychromatic418967fa.accept_13_9_6_7_1_551 35 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 162 215 (accept_3_2 34 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 162 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 162 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 162 215 (accept_3_2 31 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 162 215 (Polychromatic418967fa.accept_13_4_6_7_1_2471 30 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 215 (accept_3_2 28 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 162 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 162 215
  (Polychromatic418967fa.accept_24_2_18_23_1_11077 26 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 162 215 (accept_3_2 25 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 162 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 162 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 162 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 162
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 215 (accept_3_2 22 162
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9
  21 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 162 215
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 162 215 (accept_3_2 19 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 162 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 162 215 (accept_3_2 16 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 162 215 (Polychromatic418967fa.accept_19_15_10_6_1_7169 15 162 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 162 215
  (Polychromatic418967fa.accept_11_3_8_6_1_788 14 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 162 215 (accept_3_2 13 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 162 215 (Polychromatic418967fa.accept_13_12_6_7_1_1071 12 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 162 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 215 (accept_3_2 10 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 162 215
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 215 (accept_3_2 7 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  162 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 162 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 215 (accept_3_2 4 162 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 162 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 162 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 162 215
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 2 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 162 215 (accept_3_2 1 162 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 161 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 54 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 161 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 161 215 (Polychromatic418967fa.accept_15_8_11_5_1_169 53 161
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 215 (accept_3_2 52 161
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 215
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 161 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 161 215 (accept_3_2 49 161 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 161 215 (Polychromatic418967fa.accept_17_14_8_11_1_4052 48 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 161 215
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 47 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 161 215 (accept_3_2 46 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 161 215 (Polychromatic418967fa.accept_11_1_7_6_1_378 45 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 161 215 (Polychromatic418967fa.accept_10_4_1_5_1_1018 44 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 161 215 (accept_3_2 43 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 161 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 161 215
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 41 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 161 215 (accept_3_2 40 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 161 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 39 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 161 215 (accept_3_2 37 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 161 215 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 161 215
  (Polychromatic418967fa.accept_17_1_8_11_1_6471 35 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 161 215 (accept_3_2 34 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 161 215 (Polychromatic418967fa.accept_19_14_9_6_1_8633 33 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 161 215 (Polychromatic418967fa.accept_15_2_11_5_1_1266 32 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 161 215 (accept_3_2 31 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 161 215
  (Polychromatic418967fa.accept_10_9_1_5_1_594 29 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 161 215 (accept_3_2 28 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 161 215 (Polychromatic418967fa.accept_20_7_1_15_1_2700 27 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 161 215 (accept_3_2 25 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 161 215 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 161 215
  (Polychromatic418967fa.accept_11_1_7_6_1_378 23 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 161 215 (accept_3_2 22 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 161 215 (Polychromatic418967fa.accept_15_6_11_5_1_168 21 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 161 215 (Polychromatic418967fa.accept_21_20_14_5_1_8194 20 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 161 215 (accept_3_2 19 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 161 215
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 161 215 (accept_3_2 16 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 161 215 (Polychromatic418967fa.accept_13_2_5_7_1_1695 15 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 161 215 (accept_3_2 13 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 161 215 (Polychromatic418967fa.accept_11_1_7_6_1_378 12 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 161 215
  (Polychromatic418967fa.accept_13_11_5_7_1_2420 11 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 161 215 (accept_3_2 10 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  161 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 161 215 (Polychromatic418967fa.accept_15_8_11_5_1_169 8 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 215 (accept_3_2 7 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 215
  (Polychromatic418967fa.accept_20_5_1_15_1_3928 5 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 161 215 (accept_3_2 4 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  161 215 (Polychromatic418967fa.accept_19_3_9_6_1_12696 3 161 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 161 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 215 (accept_3_2 1 161 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 161 215))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 160 215
  (Eq.refl Bool.true) (allA_of_3_0 56 160 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 159 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 56 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 215 (accept_3_2 55 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 215
  (Polychromatic418967fa.accept_13_1_3_7_1_1710 53 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 215 (accept_3_2 52 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 215 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 215 (accept_3_2 49 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 215 (accept_3_2 46 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 215 (accept_3_2 43 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 215 (Polychromatic418967fa.accept_15_12_9_5_1_2973 42 159 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 41 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 215 (accept_3_2 40 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 215 (accept_3_2 37 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 215 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 215
  (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 215 (accept_3_2 34 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 215 (accept_3_2 31 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 29 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 215 (accept_3_2 28 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 215 (Polychromatic418967fa.accept_13_1_3_7_1_1710 27 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 215 (accept_3_2 25 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 23 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 215 (accept_3_2 22 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 215 (accept_3_2 19 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 215 (Polychromatic418967fa.accept_15_3_9_5_1_2082 18 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 215
  (Polychromatic418967fa.accept_13_4_3_7_1_2515 17 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 215 (accept_3_2 16 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 215 (Polychromatic418967fa.accept_21_15_12_5_1_9766 15 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 215 (accept_3_2 13 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 215 (accept_3_2 10 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 215 (accept_3_2 7 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 215 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 159 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 5 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 215 (accept_3_2 4 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 159 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 215 (accept_3_2 1 159 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 215))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 158 215
  (Eq.refl Bool.true) (allA_succ_of_accept 57 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 158 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 56 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 158 215 (accept_3_2 55 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 158 215 (Polychromatic418967fa.accept_21_12_11_5_1_6549 54 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 158 215 (accept_3_2 52 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 158 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 158 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 158 215 (accept_3_2 49 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 158 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 158 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 158 215 (accept_3_2 46 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 158 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 158 215 (accept_3_2 43 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 158 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 158 215 (accept_3_2 40 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 158 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 158 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 38 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 158 215 (accept_3_2 37 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 158 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 158 215 (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 215 (accept_3_2 34 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 158 215
  (Polychromatic418967fa.accept_10_2_8_5_1_587 32 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 158 215 (accept_3_2 31 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 158 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 215 (accept_3_2 28 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 158 215
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 26 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 158 215 (accept_3_2 25 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 215 (accept_3_2 22 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 215 (accept_3_2 19 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 215 (Polychromatic418967fa.accept_13_5_2_7_1_2414 18 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 215 (accept_3_2 16 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 215
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 215 (accept_3_2 13 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 215 (accept_3_2 10 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 215 (accept_3_2 7 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 215 (accept_3_2 4 158 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 158 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 215 (accept_3_2 1 158 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 157 215 (Eq.refl Bool.true) (allA_of_3_0
  59 157 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 156 215 (Eq.refl Bool.true) (allA_succ_of_accept 59
  156 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 156 215 (accept_3_2 58 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 156 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 57 156 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 156 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 56 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 156 215 (accept_3_2 55 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 156 215 (Polychromatic418967fa.accept_10_4_6_5_1_74
  54 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 156 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 156 215 (accept_3_2 52 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 156 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 156 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 50 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 156 215 (accept_3_2 49 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 156 215 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 156 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 156 215 (accept_3_2 46 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 156 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 156 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 44 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 156 215 (accept_3_2 43 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 156 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 156 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 156 215 (accept_3_2 40 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 156 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 156 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 38 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 156 215 (accept_3_2 37 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 156 215 (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 156 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 156 215 (accept_3_2 34 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 156 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 156 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 215 (accept_3_2 31 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 156 215 (Polychromatic418967fa.accept_20_10_16_15_1_1536 30 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 156 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 215 (accept_3_2 28 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 156 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 156 215 (Polychromatic418967fa.accept_11_4_2_6_1_389 26 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 215 (accept_3_2 25 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 156 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 156 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 215 (accept_3_2 22 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 156 215 (Polychromatic418967fa.accept_10_1_6_5_1_304 21 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 156 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 215 (accept_3_2 19 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 156 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 156 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 156 215 (accept_3_2 16 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 156 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 156 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 156 215 (accept_3_2 13 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 156 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 12 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 156 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 215 (accept_3_2 10 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  156 215 (Polychromatic418967fa.accept_10_9_6_5_1_1002 9 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 156 215 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 215 (accept_3_2 7 156 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 156 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 156 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 156 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 215 (accept_3_2 4 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  156 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 156 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 156 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 215 (accept_3_2 1 156 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 155
  215 (Eq.refl Bool.true) (allA_succ_of_gcd 60 155 215 5 12 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 155 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 155 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 215 (accept_3_2 58 155 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 215 (Polychromatic418967fa.accept_9_3_2_8_1_108
  57 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 215
  (Polychromatic418967fa.accept_13_4_12_7_1_2439 56 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 155 215 5 11 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 54 155 215 (Polychromatic418967fa.accept_17_3_2_11_1_1895 54 155 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 155 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 53 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 155 215 (accept_3_2 52 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 155 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 51 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 155 215 5 10 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 155 215 (accept_3_2 49 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 215 (Polychromatic418967fa.accept_13_8_12_7_1_2442 47 155
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 215 (accept_3_2 46 155
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 155 215 5 9 31 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 155 215
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 215 (accept_3_2 43 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 155 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 155 215 5 8 31 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 155 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 39 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 155 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 38 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 215 (accept_3_2 37 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 155 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 155 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 155 215 5 7 31 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 155 215 (accept_3_2 34 155 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 155 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 155 215 (accept_3_2 31 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  155 215 5 6 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 155 215 (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 155 215 (accept_3_2 28 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 215 (Polychromatic418967fa.accept_17_9_2_11_1_4042 26 155
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 215 5 5 31 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 215
  (Polychromatic418967fa.accept_7_3_1_5_1_44 24 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 155 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 215 (accept_3_2 22 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 155 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 155 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 155 215 5 4 31 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 155 215 (accept_3_2 19 155 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 155 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 215
  (Polychromatic418967fa.accept_7_3_1_5_1_44 17 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 215 (accept_3_2 16 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  155 215 5 3 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 155 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 155 215 (accept_3_2 13 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 155 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 155 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 215 5 2 31 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 215
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 9 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 215 (Polychromatic418967fa.accept_13_8_12_7_1_2442 8 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 215 (accept_3_2 7 155 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 155 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 215 5 1 31 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 215 (accept_3_2 4 155 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 155 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 215
  (Polychromatic418967fa.accept_16_2_11_7_1_2352 2 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 215 (accept_3_2 1 155 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 154 215 (Eq.refl Bool.true)
  (allA_of_3_0 62 154 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 153 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 215 (accept_3_2 61 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 153 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 215 (Polychromatic418967fa.accept_19_2_1_6_1_5780
  59 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 215 (accept_3_2 58
  153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 57 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 153 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 215 (accept_3_2 55 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 215 (Polychromatic418967fa.accept_7_4_6_5_1_141
  53 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 215 (accept_3_2 52
  153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 215
  (Polychromatic418967fa.accept_12_3_9_11_1_231 51 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 215 (accept_3_2 49 153 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 153 215 (Polychromatic418967fa.accept_10_8_3_5_1_613 48 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 215
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 153 215 (accept_3_2 46 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 153 215 (Polychromatic418967fa.accept_16_13_9_7_1_4532 45 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 153 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 215 (accept_3_2 43 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 215
  (Polychromatic418967fa.accept_19_3_1_6_1_3114 41 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 215 (accept_3_2 40 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 215 (accept_3_2 37 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 215
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 35 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 215 (accept_3_2 34 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 153 215 (Polychromatic418967fa.accept_18_15_9_17_1_6043 33 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 153 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 215 (accept_3_2 31 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 29 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 215 (accept_3_2 28 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 153 215 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 215 (accept_3_2 25 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 215 (Polychromatic418967fa.accept_15_9_3_5_1_2077 24 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 215
  (Polychromatic418967fa.accept_15_8_3_5_1_608 23 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 215 (accept_3_2 22 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 215 (Polychromatic418967fa.accept_13_8_10_7_1_1702 21 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 215 (accept_3_2 19 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 215
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 215 (accept_3_2 16 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 215 (accept_3_2 13 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 11 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 215 (accept_3_2 10 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 215 (Polychromatic418967fa.accept_15_9_3_5_1_2077 9 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 215 (accept_3_2 7 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 153 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 215
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 215 (accept_3_2 4 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 3 153 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 215 (accept_3_2 1 153 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64
  152 215 (Eq.refl Bool.true) (allA_succ_of_accept 63 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 152 215
  (Polychromatic418967fa.accept_12_2_8_11_1_31 62 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 152 215 (accept_3_2 61 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 152 215 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 152 215 (Polychromatic418967fa.accept_14_3_12_5_1_153 59 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 152 215 (accept_3_2 58 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 152 215
  (Polychromatic418967fa.accept_13_4_9_7_1_2402 56 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 152 215 (accept_3_2 55 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 152 215 (Polychromatic418967fa.accept_13_2_9_7_1_164 54 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 152 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 152 215 (accept_3_2 52 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 152 215
  (Polychromatic418967fa.accept_12_2_8_11_1_31 50 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 152 215 (accept_3_2 49 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 152 215 (Polychromatic418967fa.accept_10_8_2_5_1_596 48 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 152 215 (Polychromatic418967fa.accept_10_7_2_5_1_298 47 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 152 215 (accept_3_2 46 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 152 215
  (Polychromatic418967fa.accept_15_14_2_5_1_1272 44 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 152 215 (accept_3_2 43 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 152 215 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 152 215 (Polychromatic418967fa.accept_13_2_9_7_1_164 41 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 215 (accept_3_2 40 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 215
  (Polychromatic418967fa.accept_10_8_2_5_1_596 38 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 152 215 (accept_3_2 37 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 152 215 (Polychromatic418967fa.accept_11_3_9_6_1_105 36 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 152 215 (Polychromatic418967fa.accept_14_7_12_5_1_1861 35 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 215 (accept_3_2 34 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 215
  (Polychromatic418967fa.accept_13_6_9_7_1_2430 32 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 215 (accept_3_2 31 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 215 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 215 (Polychromatic418967fa.accept_13_3_9_7_1_1730 29 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 215 (accept_3_2 28 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 215
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 215 (accept_3_2 25 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 215 (Polychromatic418967fa.accept_13_11_9_7_1_2484 24 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 23 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 215 (accept_3_2 22 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 215
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 20 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 215 (accept_3_2 19 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 215 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 215 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 215 (accept_3_2 16 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 215
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 215 (accept_3_2 13 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 215 (Polychromatic418967fa.accept_15_12_2_5_1_3939 12 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 215 (Polychromatic418967fa.accept_13_11_9_7_1_2484 11 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 215 (accept_3_2 10 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 215
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 215 (accept_3_2 7 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 215 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 215 (Polychromatic418967fa.accept_17_5_16_11_1_3998 5 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 215 (accept_3_2 4 152 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 152 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 215
  (Polychromatic418967fa.accept_12_2_8_11_1_31 2 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 215 (accept_3_2 1 152 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 151 215 (Eq.refl Bool.true)
  (allA_of_3_0 65 151 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 150 215 (Eq.refl Bool.true)
  (allA_succ_of_gcd 65 150 215 5 13 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 150 215 (accept_3_2 64 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 150 215 (Polychromatic418967fa.accept_16_15_6_7_1_4512 63 150 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 150 215 (Polychromatic418967fa.accept_20_2_10_15_1_3953 62 150
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 150 215 (accept_3_2 61 150
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 150 215 5 12 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 150 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 59 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 150 215 (accept_3_2 58 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 150 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 56 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 150 215 5 11 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 150 215
  (Polychromatic418967fa.accept_14_12_10_5_1_2712 54 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 150 215 (accept_3_2 52 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 150 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 150 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 150 215 5 10 30 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 150 215 (accept_3_2 49 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 150 215 (Polychromatic418967fa.accept_9_3_6_8_1_308
  48 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 150 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 47 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 150 215 (accept_3_2 46 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  150 215 5 9 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 150 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 150 215 (accept_3_2 43 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 150 215 (Polychromatic418967fa.accept_17_8_14_11_1_9101 42 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 215 5 8 30 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 215
  (Polychromatic418967fa.accept_9_3_6_8_1_308 39 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 150 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 150 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 150 215 (accept_3_2 37 150 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 150 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 150 215 5 7 30 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 150 215 (accept_3_2 34 150 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 150 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 32 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 215 (accept_3_2 31 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  150 215 5 6 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 150 215 (accept_3_2 28 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 150 215 (Polychromatic418967fa.accept_19_8_17_6_1_5728 27 150 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 150 215 (Polychromatic418967fa.accept_14_12_10_5_1_2712 26 150
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 150 215 5 5 30 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 150 215
  (Polychromatic418967fa.accept_20_4_10_15_1_6919 24 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 150 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 215 (accept_3_2 22 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 150 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 150 215 5 4 30 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 215 (accept_3_2 19 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 150 215
  (Polychromatic418967fa.accept_19_18_17_6_1_5775 18 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 215 (accept_3_2 16 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 215 5 3 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 215 (accept_3_2 13 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 150 215 (Polychromatic418967fa.accept_9_3_6_8_1_308
  12 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 150 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 11 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 215 5 2 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 150 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 150 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 150 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 215 (accept_3_2 7 150 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 150 215
  (Polychromatic418967fa.accept_20_6_10_15_1_6879 6 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 150 215 5 1 30 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 150 215 (accept_3_2 4 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  150 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 150 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 150 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 215 (accept_3_2 1 150 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 150 215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  67 149 215 (Eq.refl Bool.true) (allA_succ_of_accept 66 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 149 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 215 (accept_3_2 64 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 215 (Polychromatic418967fa.accept_14_7_9_5_1_529 63 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 215 (accept_3_2 61 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 215 (accept_3_2 58 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 215 (accept_3_2 55 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 53 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 215 (accept_3_2 52 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 215 (accept_3_2 49 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 215 (accept_3_2 46 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 45 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 44 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 215 (accept_3_2 43 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 215
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 215 (accept_3_2 40 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 39 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 215 (accept_3_2 37 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 215 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 215
  (Polychromatic418967fa.accept_13_9_6_7_1_551 35 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 215 (accept_3_2 34 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 32 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 215 (accept_3_2 31 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 215 (accept_3_2 28 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 215 (Polychromatic418967fa.accept_13_1_6_7_1_550 27 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 215 (accept_3_2 25 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 215
  (Polychromatic418967fa.accept_15_8_14_5_1_2089 23 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 215 (accept_3_2 22 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 215 (accept_3_2 19 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 215 (accept_3_2 16 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 215 (accept_3_2 13 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 11 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 215 (accept_3_2 10 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 215 (Polychromatic418967fa.accept_13_9_6_7_1_551 9 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 215 (Polychromatic418967fa.accept_15_8_14_5_1_2089 8 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 215 (accept_3_2 7 149 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 215
  (Polychromatic418967fa.accept_20_5_9_15_1_3973 5 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 215 (accept_3_2 4 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 149 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 215 (accept_3_2 1 149 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  68 148 215 (Eq.refl Bool.true) (allA_of_3_0 68 148 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 147 215
  (Eq.refl Bool.true) (allA_succ_of_accept 68 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 68 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 215 (accept_3_2 67 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 215 (Polychromatic418967fa.accept_15_6_12_5_1_2108 66 147
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 65 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 215 (accept_3_2 64 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 215 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 215 (accept_3_2 61 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 59 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 215 (accept_3_2 58 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 215 (Polychromatic418967fa.accept_11_2_4_6_1_2412 57 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 215 (accept_3_2 55 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 215 (Polychromatic418967fa.accept_14_12_7_5_1_1107 54 147 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 215
  (Polychromatic418967fa.accept_10_3_7_5_1_288 53 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 215 (accept_3_2 52 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 50 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 215 (accept_3_2 49 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 215 (Polychromatic418967fa.accept_10_8_7_5_1_602 48 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 47 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 215 (accept_3_2 46 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 45 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 44 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 215 (accept_3_2 43 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 41 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 215 (accept_3_2 40 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 215 (Polychromatic418967fa.accept_15_9_12_5_1_1267 39 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 38 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 215 (accept_3_2 37 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 215
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 215 (accept_3_2 34 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 215 (accept_3_2 31 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 215 (Polychromatic418967fa.accept_14_2_7_5_1_5450 30 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 29 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 215 (accept_3_2 28 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 215 (Polychromatic418967fa.accept_16_11_3_7_1_2375 27 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 215 (accept_3_2 25 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 23 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 215 (accept_3_2 22 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 20 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 215 (accept_3_2 19 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 215 (Polychromatic418967fa.accept_10_8_7_5_1_602 18 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 215
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 17 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 215 (accept_3_2 16 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 215 (accept_3_2 13 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 215 (accept_3_2 10 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 9 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 215 (accept_3_2 7 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 5 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 215 (accept_3_2 4 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 215 (Polychromatic418967fa.accept_10_3_7_5_1_288 3 147 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 2 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 215 (accept_3_2 1 147 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 70 146 215 (Eq.refl Bool.true) (allA_succ_of_accept 69 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9
  69 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 146 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 146 215 (accept_3_2 67 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 146 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 66 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 146 215 (accept_3_2 64 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 146 215
  (Polychromatic418967fa.accept_13_10_3_7_1_2517 62 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 146 215 (accept_3_2 61 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 146 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 146 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 59 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 146 215 (accept_3_2 58 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 146 215
  (Polychromatic418967fa.accept_12_8_2_11_1_246 56 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 146 215 (accept_3_2 55 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 146 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 146 215 (accept_3_2 52 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 146 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 146 215 (accept_3_2 49 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 215 (Polychromatic418967fa.accept_13_8_3_7_1_2455 47 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 215 (accept_3_2 46 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 215
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 215 (accept_3_2 43 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 215 (accept_3_2 40 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 215
  (Polychromatic418967fa.accept_15_8_11_5_1_169 38 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 215 (accept_3_2 37 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 215 (Polychromatic418967fa.accept_13_9_3_7_1_1065 35 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 215 (accept_3_2 34 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 215 (accept_3_2 31 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 215 (accept_3_2 28 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 215
  (Polychromatic418967fa.accept_18_8_2_17_1_4782 26 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 215 (accept_3_2 25 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 215 (accept_3_2 22 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 215
  (Polychromatic418967fa.accept_11_9_3_6_1_797 20 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 215 (accept_3_2 19 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 215 (accept_3_2 16 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 215 (accept_3_2 13 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 215 (accept_3_2 10 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 215 (accept_3_2 7 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 215 (accept_3_2 4 146 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 146 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 215
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 2 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 215 (accept_3_2 1 146 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 145 215 (Eq.refl Bool.true)
  (allA_of_3_0 71 145 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 144 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 144 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 71 144 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 144 215 (accept_3_2 70 144 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 144 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 69 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 144 215 (Polychromatic418967fa.accept_13_3_1_7_1_1706
  68 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 144 215 (accept_3_2 67
  144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 144 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 66 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 144 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 65 144 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 144 215 (accept_3_2 64 144 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 144 215 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 144 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 62 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 144 215 (accept_3_2 61 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 144 215 (Polychromatic418967fa.accept_11_5_1_6_1_774 60 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 144 215 (Polychromatic418967fa.accept_10_9_4_5_1_616 59 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 144 215 (accept_3_2 58 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 144 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 57 144 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 144 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 144 215 (accept_3_2 55 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 144 215 (Polychromatic418967fa.accept_19_16_11_6_1_7149 54 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 144 215 (Polychromatic418967fa.accept_17_2_8_11_1_1041 53 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 144 215 (accept_3_2 52 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 144 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 51 144 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 144 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 50 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 215 (accept_3_2 49 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 144 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 144 215 (Polychromatic418967fa.accept_13_8_1_7_1_2505 47 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 215 (accept_3_2 46 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 144 215 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 144
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 144 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 44 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 144 215 (accept_3_2 43 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 144 215 (Polychromatic418967fa.accept_13_3_1_7_1_1706 42 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 144 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 41 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 215 (accept_3_2 40 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 144 215 (Polychromatic418967fa.accept_10_9_4_5_1_616 39 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 144 215
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 144 215 (accept_3_2 37 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 144 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 144 215 (Polychromatic418967fa.accept_17_1_8_11_1_6471 35 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 144 215 (accept_3_2 34 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 144 215 (Polychromatic418967fa.accept_15_3_9_5_1_2082 33 144
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 144 215
  (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 144 215 (accept_3_2 31 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 144 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 30 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 144 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 29 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 144 215 (accept_3_2 28 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 144 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 144 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 144 215 (accept_3_2 25 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 144 215 (Polychromatic418967fa.accept_13_11_1_7_1_1691 24 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 144 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 23 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 215 (accept_3_2 22 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 144 215 (Polychromatic418967fa.accept_10_1_4_5_1_1031 21 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 144 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 20 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 215 (accept_3_2 19 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 144 215 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 144 215 (Polychromatic418967fa.accept_19_17_11_6_1_9996 17 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 215 (accept_3_2 16 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 144 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 144 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 144 215
  (Polychromatic418967fa.accept_15_14_9_5_1_3932 14 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 215 (accept_3_2 13 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 144 215 (Polychromatic418967fa.accept_15_12_9_5_1_2973 12 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 144 215 (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 215 (accept_3_2 10 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 144 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 144 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 144 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 8 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 215 (accept_3_2 7 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  144 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 6 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 144 215 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 215 (accept_3_2 4 144 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 144 215 (Polychromatic418967fa.accept_13_3_1_7_1_1706 3 144 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 144 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 215 (accept_3_2 1 144 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 143 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 72 143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 143 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 215 (accept_3_2 70 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 143 215
  (Polychromatic418967fa.accept_17_1_7_11_1_2892 69 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 143 215 (Polychromatic418967fa.accept_10_8_3_5_1_613 68 143 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 215 (accept_3_2 67 143 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 143 215 (Polychromatic418967fa.accept_19_9_10_6_1_4394 66 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 143 215
  (Polychromatic418967fa.accept_7_2_3_5_1_34 65 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 143 215 (accept_3_2 64 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 143 215 (Polychromatic418967fa.accept_15_3_8_5_1_2105 63 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 143 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 62 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 215 (accept_3_2 61 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 215 (Polychromatic418967fa.accept_22_16_11_17_1_12695 60
  143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 215
  (Polychromatic418967fa.accept_15_14_8_5_1_2104 59 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 143 215 (accept_3_2 58 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 143 215 (Polychromatic418967fa.accept_15_11_8_5_1_1278 56 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 143 215 (accept_3_2 55 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 143 215 (Polychromatic418967fa.accept_14_12_3_5_1_1868 54 143
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 215
  (Polychromatic418967fa.accept_19_15_10_6_1_7169 53 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 143 215 (accept_3_2 52 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 143 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 50 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 143 215 (accept_3_2 49 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 143 215 (Polychromatic418967fa.accept_10_8_3_5_1_613
  48 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 143 215
  (Polychromatic418967fa.accept_10_7_3_5_1_301 47 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 143 215 (accept_3_2 46 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 143 215 (Polychromatic418967fa.accept_20_5_3_15_1_6909 45 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 44 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 143 215 (accept_3_2 43 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 143 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 143 215
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 41 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 143 215 (accept_3_2 40 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 143 215 (Polychromatic418967fa.accept_17_5_7_11_1_5274 39 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 143 215 (Polychromatic418967fa.accept_10_8_3_5_1_613 38 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 215 (accept_3_2 37 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 215
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 35 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 215 (accept_3_2 34 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 215 (Polychromatic418967fa.accept_15_3_8_5_1_2105 33 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 215 (accept_3_2 31 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 30 143 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 215
  (Polychromatic418967fa.accept_7_1_3_5_1_33 29 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 215 (accept_3_2 28 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 215 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 215 (Polychromatic418967fa.accept_14_12_3_5_1_1868 26 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 215 (accept_3_2 25 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 215 (Polychromatic418967fa.accept_16_8_15_7_1_5658 24 143
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 215
  (Polychromatic418967fa.accept_7_2_3_5_1_34 23 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 215 (accept_3_2 22 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 215 (Polychromatic418967fa.accept_19_2_10_6_1_4373 21 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 215 (Polychromatic418967fa.accept_19_1_10_6_1_5726 20 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 215 (accept_3_2 19 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 215 (Polychromatic418967fa.accept_10_8_3_5_1_613 18 143
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 215
  (Polychromatic418967fa.accept_10_7_3_5_1_301 17 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 215 (accept_3_2 16 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 215 (Polychromatic418967fa.accept_15_14_8_5_1_2104 14 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 215 (accept_3_2 13 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 215 (Polychromatic418967fa.accept_10_2_3_5_1_996 12 143
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 215
  (Polychromatic418967fa.accept_15_11_8_5_1_1278 11 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 215 (accept_3_2 10 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 215 (accept_3_2 7 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 215 (Polychromatic418967fa.accept_16_6_15_7_1_1510 6 143 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 215
  (Polychromatic418967fa.accept_17_5_7_11_1_5274 5 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 215 (accept_3_2 4 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 215 (Polychromatic418967fa.accept_15_3_8_5_1_2105 3 143 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 215 (accept_3_2 1 143 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 74 142 215 (Eq.refl Bool.true) (allA_of_3_0 74 142 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 75 141 215 (Eq.refl Bool.true) (allA_succ_of_accept 74 141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27
  74 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 215 (accept_3_2 73
  141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 215
  (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 141 215 (Polychromatic418967fa.accept_15_11_6_5_1_1295 71 141 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 215 (accept_3_2 70 141 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 141 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 69 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 68
  141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 215 (accept_3_2 67
  141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 66 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 141 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 141 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 215 (accept_3_2 64 141 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 141 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 215 (accept_3_2 61 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 141 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 215 (accept_3_2 58 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 57 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 141 215 (accept_3_2 55 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 141 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 53 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 215 (accept_3_2 52 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 51 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 215 (accept_3_2 49 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 141 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 141 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 215 (accept_3_2 46 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 45 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 215 (accept_3_2 43 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 41 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 215 (accept_3_2 40 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 39 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 215 (accept_3_2 37 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 141 215 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 141 215 (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 215 (accept_3_2 34 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 215 (Polychromatic418967fa.accept_15_3_6_5_1_2079 33 141
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 215 (accept_3_2 31 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 215 (accept_3_2 28 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 27 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 215 (accept_3_2 25 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 215 (accept_3_2 22 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 215 (accept_3_2 19 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 215 (accept_3_2 16 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 15 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 215 (accept_3_2 13 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 215 (accept_3_2 10 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 215 (accept_3_2 7 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 215 (accept_3_2 4 141 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 141 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 215 (accept_3_2 1 141 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 140 215 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 140 215 5 15 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 140 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 140 215 (accept_3_2 73 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 140 215 (Polychromatic418967fa.accept_16_8_12_7_1_2399 72 140
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 140 215
  (Polychromatic418967fa.accept_19_14_7_6_1_8654 71 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 140 215 5 14 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 140 215
  (Polychromatic418967fa.accept_13_3_10_7_1_1061 68 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 140 215 (accept_3_2 67 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 140 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 140 215 5 13 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 140 215 (accept_3_2 64 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 140 215 (Polychromatic418967fa.accept_12_2_8_11_1_31 62 140
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 140 215 (accept_3_2 61 140
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 140 215 5 12 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 140 215
  (Polychromatic418967fa.accept_8_3_4_7_1_475 59 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 140 215 (accept_3_2 58 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 140 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 140 215 5 11 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 140 215
  (Polychromatic418967fa.accept_19_16_7_6_1_7201 54 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 140 215 (Polychromatic418967fa.accept_16_5_12_7_1_3411 53 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 140 215 (accept_3_2 52 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 140 215 5 10 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 140 215 (accept_3_2 49 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 140 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 140 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 140 215 (accept_3_2 46 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  140 215 5 9 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 140 215 (Polychromatic418967fa.accept_17_10_4_11_1_4047 44 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 140 215 (accept_3_2 43 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 140 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 140 215 (Polychromatic418967fa.accept_19_3_7_6_1_5791 41 140
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 215 5 8 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 39 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 140 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 215 (accept_3_2 37 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 140 215 (Polychromatic418967fa.accept_11_3_8_6_1_788 36 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 140 215 5 7 28 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 140 215 (accept_3_2 34 140 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 33
  140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 215
  (Polychromatic418967fa.accept_17_15_4_11_1_6515 32 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 140 215 (accept_3_2 31 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 215 5 6 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 140 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 215 (accept_3_2 28 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 215 (Polychromatic418967fa.accept_12_2_8_11_1_31
  26 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 140 215 5 5 28 43
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 140 215
  (Polychromatic418967fa.accept_9_6_5_8_1_598 24 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 140 215 (Polychromatic418967fa.accept_17_6_4_11_1_4072 23 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 215 (accept_3_2 22 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 215 5 4 28 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 215 (accept_3_2 19 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 215 (Polychromatic418967fa.accept_16_2_12_7_1_3410 18 140
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 215
  (Polychromatic418967fa.accept_13_4_10_7_1_1701 17 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 215 (accept_3_2 16 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  140 215 5 3 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 140 215 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 140 215 (accept_3_2 13 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 140 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 140 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 215 5 2 28 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 215
  (Polychromatic418967fa.accept_6_3_2_5_1_32 9 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 215 (Polychromatic418967fa.accept_13_8_10_7_1_1702 8 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 215 (accept_3_2 7 140 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 140 215 5 1 28 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 140 215 (accept_3_2 4 140 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 140 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 215 (accept_3_2 1 140 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 139 215 (Eq.refl
  Bool.true) (allA_of_3_0 77 139 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 138 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 138 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 138 215 (accept_3_2 76 138 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 138 215 (Polychromatic418967fa.accept_13_10_8_7_1_1074 75 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 138 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 74 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 138 215 (accept_3_2 73 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 138 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 138 215 (Polychromatic418967fa.accept_17_3_2_11_1_1895 71 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 138 215 (accept_3_2 70 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 138 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 138 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 68 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 138 215 (accept_3_2 67 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 138 215 (Polychromatic418967fa.accept_13_1_8_7_1_1088 66 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 138 215 (accept_3_2 64 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 138 215 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 138 215
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 138 215 (accept_3_2 61 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 138 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 138 215 (accept_3_2 58 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 138 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 56 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 138 215 (accept_3_2 55 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 138 215 (Polychromatic418967fa.accept_13_2_8_7_1_2424 54 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 215 (accept_3_2 52 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 51 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 138 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 50 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 215 (accept_3_2 49 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 138 215 (Polychromatic418967fa.accept_13_9_8_7_1_1073 48 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 138 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 215 (accept_3_2 46 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 138 215
  (Polychromatic418967fa.accept_25_19_13_15_1_5391 44 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 138 215 (accept_3_2 43 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 42 138 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 138 215 (accept_3_2 40 138 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 138 215 (Polychromatic418967fa.accept_15_9_3_5_1_2077
  39 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 138 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 38 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 138 215 (accept_3_2 37 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 138 215 (Polychromatic418967fa.accept_13_10_8_7_1_1074 36 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 138 215 (Polychromatic418967fa.accept_13_9_8_7_1_1073 35 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 215 (accept_3_2 34 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 138 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 138 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 32 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 215 (accept_3_2 31 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 138 215 (Polychromatic418967fa.accept_16_14_10_7_1_2363 30 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 215 (accept_3_2 28 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 138 215 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 138 215
  (Polychromatic418967fa.accept_17_9_2_11_1_4042 26 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 138 215 (accept_3_2 25 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 138 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 215 (accept_3_2 22 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 138 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 20 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 215 (accept_3_2 19 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 138 215 (Polychromatic418967fa.accept_19_18_5_6_1_2004 18 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 215 (accept_3_2 16 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 138 215
  (Polychromatic418967fa.accept_9_5_3_8_1_316 14 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 215 (accept_3_2 13 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 138 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 12 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 138 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 215 (accept_3_2 10 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 138 215
  (Polychromatic418967fa.accept_15_8_3_5_1_608 8 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 138 215 (accept_3_2 7 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  138 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 138 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 215 (accept_3_2 4 138 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 138 215 (Polychromatic418967fa.accept_10_3_8_5_1_606 3 138 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 138 215
  (Polychromatic418967fa.accept_9_2_3_8_1_318 2 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 215 (accept_3_2 1 138 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 137 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 78 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 215 (Polychromatic418967fa.accept_9_5_2_8_1_109
  77 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 215 (accept_3_2 76
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 215
  (Polychromatic418967fa.accept_9_3_2_8_1_108 75 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 215 (accept_3_2 73 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 137 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 72 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 137 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 71
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 215 (accept_3_2 70
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 69 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 137 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 68 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 215 (accept_3_2 67 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 137 215 (Polychromatic418967fa.accept_7_2_4_5_1_313
  65 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 215 (accept_3_2 64
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 215
  (Polychromatic418967fa.accept_10_3_7_5_1_288 63 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 215 (accept_3_2 61 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 137 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 60 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 137 215 (Polychromatic418967fa.accept_9_5_2_8_1_109
  59 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 215 (accept_3_2 58
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 57 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 137 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 215 (accept_3_2 55 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 215 (Polychromatic418967fa.accept_10_3_7_5_1_288
  53 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 215 (accept_3_2 52
  137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 51 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 215 (accept_3_2 49 137 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 137 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 48 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 215
  (Polychromatic418967fa.accept_22_3_5_17_1_9702 47 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 215 (accept_3_2 46 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 44 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 215 (accept_3_2 43 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 215
  (Polychromatic418967fa.accept_7_6_4_5_1_314 41 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 215 (accept_3_2 40 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 39 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 215 (accept_3_2 37 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 36 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 215
  (Polychromatic418967fa.accept_16_3_9_7_1_6842 35 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 215 (accept_3_2 34 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 33 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 215 (accept_3_2 31 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 215
  (Polychromatic418967fa.accept_7_1_4_5_1_35 29 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 215 (accept_3_2 28 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 27 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 215 (accept_3_2 25 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 215
  (Polychromatic418967fa.accept_7_2_4_5_1_313 23 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 215 (accept_3_2 22 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 21 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 215 (Polychromatic418967fa.accept_7_6_4_5_1_314 20 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 215 (accept_3_2 19 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 215
  (Polychromatic418967fa.accept_19_17_4_6_1_5810 17 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 215 (accept_3_2 16 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 15 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 215 (accept_3_2 13 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 215
  (Polychromatic418967fa.accept_15_11_2_5_1_2076 11 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 215 (accept_3_2 10 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 215 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 215 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 215 (accept_3_2 7 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 215 (accept_3_2 4 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 137 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 215 (accept_3_2 1 137 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 136 215 (Eq.refl Bool.true) (allA_of_3_0 80 136 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 81 135 215 (Eq.refl Bool.true) (allA_succ_of_gcd 80 135 215 5 16 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 135 215 (accept_3_2 79 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 215 (Polychromatic418967fa.accept_21_15_9_5_1_6588 78 135
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 215
  (Polychromatic418967fa.accept_13_12_5_7_1_1696 77 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 215 (accept_3_2 76 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75
  135 215 5 15 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 74 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 215 (accept_3_2 73 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 135 215 (Polychromatic418967fa.accept_19_15_2_6_1_7179 72 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 215
  (Polychromatic418967fa.accept_22_5_3_17_1_9592 71 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 135 215 5 14 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 135 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 69 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 215 (accept_3_2 67 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 135 215 5 13 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 135 215 (accept_3_2 64 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 135 215 (Polychromatic418967fa.accept_11_8_3_6_1_1855 63 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 62 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 215 (accept_3_2 61 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 135 215 5 12 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 135 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 59 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 215 (accept_3_2 58 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 57 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 56 135 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 135 215 5 11 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 135 215
  (Polychromatic418967fa.accept_13_2_5_7_1_1695 54 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 135 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 215 (accept_3_2 52 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 135 215 (Polychromatic418967fa.accept_13_12_5_7_1_1696 51 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 135 215 5 10 27 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 135 215 (accept_3_2 49 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 215
  (Polychromatic418967fa.accept_17_14_16_11_1_3997 48 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 215 (Polychromatic418967fa.accept_26_21_5_7_1_12694 47 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 215 (accept_3_2 46 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 215 5 9 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 44
  135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 215 (accept_3_2 43
  135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 215
  (Polychromatic418967fa.accept_11_9_3_6_1_797 42 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 135 215 (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 215 5 8 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 135 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 39
  135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 38 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 215 (accept_3_2 37 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 215 (Polychromatic418967fa.accept_21_15_9_5_1_6588 36 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 35 135 215 5 7 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 135 215 (accept_3_2 34 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 135 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 33 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 32 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 215 (accept_3_2 31 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 215 5 6 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 215
  (Polychromatic418967fa.accept_17_12_16_11_1_7885 29 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 135 215 (accept_3_2 28 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 135 215 (Polychromatic418967fa.accept_19_8_2_6_1_8677 27 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 26 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 135 215 5 5 27 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 135 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 24 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 135 215 (Polychromatic418967fa.accept_19_4_2_6_1_7181 23 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 215 (accept_3_2 22 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 135 215 (Polychromatic418967fa.accept_12_9_3_11_1_1097 21 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 135 215 5 4 27 43 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 215 (accept_3_2 19 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 215 (Polychromatic418967fa.accept_7_4_2_5_1_527
  18 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 215 (accept_3_2 16 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  135 215 5 3 27 43 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 14 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 135 215 (accept_3_2 13 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 135 215 (Polychromatic418967fa.accept_13_12_5_7_1_1696 12 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 135 215 5 2 27 43 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 135 215
  (Polychromatic418967fa.accept_11_9_3_6_1_797 9 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 135 215 (Polychromatic418967fa.accept_6_2_3_5_1_26 8 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 215 (accept_3_2 7 135 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 135 215 (Polychromatic418967fa.accept_25_6_10_15_1_12693 6 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 135 215 5 1 27 43 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 215 (accept_3_2 4 135 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 135 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 2 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 215 (accept_3_2 1 135 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 134 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 134 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 80
  134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 134 215 (accept_3_2 79
  134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 134 215
  (Polychromatic418967fa.accept_19_2_1_6_1_5780 78 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 134 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 134 215 (accept_3_2 76 134 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 134 215 (Polychromatic418967fa.accept_7_4_1_5_1_540
  74 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 134 215 (accept_3_2 73
  134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 134 215
  (Polychromatic418967fa.accept_17_4_15_11_1_6465 72 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 134 215 (Polychromatic418967fa.accept_10_1_4_5_1_1031 71 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 134 215 (accept_3_2 70 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 134 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 134 215
  (Polychromatic418967fa.accept_12_8_2_11_1_246 68 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 134 215 (accept_3_2 67 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 134 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 66 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 134 215 (accept_3_2 64 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 134 215
  (Polychromatic418967fa.accept_7_6_1_5_1_322 62 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 134 215 (accept_3_2 61 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 60 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 59 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 215 (accept_3_2 58 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 215 (accept_3_2 55 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 215 (Polychromatic418967fa.accept_15_9_14_5_1_2086 54 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 215 (accept_3_2 52 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 215
  (Polychromatic418967fa.accept_13_11_4_7_1_2419 50 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 215 (accept_3_2 49 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 48 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 215 (Polychromatic418967fa.accept_15_2_14_5_1_2072 47 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 215 (accept_3_2 46 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 215
  (Polychromatic418967fa.accept_12_8_2_11_1_246 44 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 215 (accept_3_2 43 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 215 (Polychromatic418967fa.accept_13_3_4_7_1_1711 42 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 215 (accept_3_2 40 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 215
  (Polychromatic418967fa.accept_7_3_1_5_1_44 38 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 215 (accept_3_2 37 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 215 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 215 (Polychromatic418967fa.accept_13_9_4_7_1_1694 35 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 215 (accept_3_2 34 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 215
  (Polychromatic418967fa.accept_7_4_1_5_1_540 32 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 215 (accept_3_2 31 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 215 (Polychromatic418967fa.accept_17_13_15_11_1_2936 30 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 215 (accept_3_2 28 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 134 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 215
  (Polychromatic418967fa.accept_10_6_4_5_1_615 26 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 215 (accept_3_2 25 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 215 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 215 (Polychromatic418967fa.accept_13_10_4_7_1_2465 23 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 215 (accept_3_2 22 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 215
  (Polychromatic418967fa.accept_7_6_1_5_1_322 20 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 215 (accept_3_2 19 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 215 (accept_3_2 16 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 215
  (Polychromatic418967fa.accept_19_14_1_6_1_5806 14 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 215 (accept_3_2 13 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 215 (Polychromatic418967fa.accept_13_12_4_7_1_2520 12 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 215 (Polychromatic418967fa.accept_7_4_1_5_1_540 11 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 215 (accept_3_2 10 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 215
  (Polychromatic418967fa.accept_12_8_2_11_1_246 8 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 215 (accept_3_2 7 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 215 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 215 (accept_3_2 4 134 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 134 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 215
  (Polychromatic418967fa.accept_15_2_14_5_1_2072 2 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 215 (accept_3_2 1 134 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 133 215 (Eq.refl
  Bool.true) (allA_of_3_0 83 133 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 132 215 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 83 132 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 132 215 (accept_3_2 82 132 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 81 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 132 215
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 80 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 132 215 (accept_3_2 79 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 78 132 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 132 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 77 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 132 215 (accept_3_2 76 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475
  75 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 132 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 74 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 132 215 (accept_3_2 73 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 132 215 (Polychromatic418967fa.accept_16_8_4_7_1_3390 72 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 71 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 132 215 (accept_3_2 70 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 132 215 (Polychromatic418967fa.accept_14_13_6_5_1_1853 69 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 132 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 68 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 132 215 (accept_3_2 67 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 132 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 66 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 132 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 65 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 132 215 (accept_3_2 64 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 132 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 132 215
  (Polychromatic418967fa.accept_15_2_12_5_1_2107 62 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 132 215 (accept_3_2 61 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 60 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 215 (accept_3_2 58 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 57 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 132 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 56 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 132 215 (accept_3_2 55 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 132 215 (Polychromatic418967fa.accept_15_9_12_5_1_1267 54 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 53 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 215 (accept_3_2 52 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 132 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 50 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 132 215 (accept_3_2 49 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 132 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 48 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 132 215 (Polychromatic418967fa.accept_9_2_6_8_1_321 47 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 215 (accept_3_2 46 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 132 215 (Polychromatic418967fa.accept_16_13_4_7_1_1537 45 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 132 215
  (Polychromatic418967fa.accept_13_5_2_7_1_2414 44 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 215 (accept_3_2 43 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 132 215 (Polychromatic418967fa.accept_24_18_12_23_1_12692 42 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 132 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 41 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 215 (accept_3_2 40 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 39 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 132 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 38 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 215 (accept_3_2 37 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 36 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 215 (accept_3_2 34 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 132 215 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 132 215
  (Polychromatic418967fa.accept_7_4_6_5_1_141 32 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 132 215 (accept_3_2 31 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 132 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 30 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 29 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 215 (accept_3_2 28 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 132 215
  (Polychromatic418967fa.accept_19_7_18_6_1_3095 26 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 215 (accept_3_2 25 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 132 215 (Polychromatic418967fa.accept_15_9_12_5_1_1267 24 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 132 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 23 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 215 (accept_3_2 22 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 132 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 132 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 20 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 132 215 (accept_3_2 19 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 132 215 (Polychromatic418967fa.accept_10_7_2_5_1_298 17 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 132 215 (accept_3_2 16 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 132 215 (Polychromatic418967fa.accept_7_1_6_5_1_39 15 132 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 132 215
  (Polychromatic418967fa.accept_9_5_6_8_1_101 14 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 132 215 (accept_3_2 13 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 132 215 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 132 215 (Polychromatic418967fa.accept_7_4_6_5_1_141 11 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 215 (accept_3_2 10 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 132 215 (Polychromatic418967fa.accept_13_9_2_7_1_1083 9 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 132 215
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 215 (accept_3_2 7 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  132 215 (Polychromatic418967fa.accept_15_6_12_5_1_2108 6 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 132 215 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 215 (accept_3_2 4 132 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 132 215 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 132 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 132 215
  (Polychromatic418967fa.accept_9_2_6_8_1_321 2 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 215 (accept_3_2 1 132 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 131 215
  (Eq.refl Bool.true) (allA_succ_of_accept 84 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 84 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 83 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 215 (accept_3_2 82 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 215 (Polychromatic418967fa.accept_13_3_1_7_1_1706 81 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 215 (Polychromatic418967fa.accept_18_8_5_17_1_1388 80 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 215 (accept_3_2 79 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 78 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 215
  (Polychromatic418967fa.accept_15_2_11_5_1_1266 77 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 131 215 (accept_3_2 76 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 75 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 131 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 74 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 215 (accept_3_2 73 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 215 (Polychromatic418967fa.accept_22_6_21_17_1_12691 72 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 131 215
  (Polychromatic418967fa.accept_11_5_10_6_1_793 71 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 131 215 (accept_3_2 70 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 69 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 68 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 131 215 (accept_3_2 67 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 66 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 65 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 131 215 (accept_3_2 64 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 215 (Polychromatic418967fa.accept_13_11_1_7_1_1691 63 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 215 (Polychromatic418967fa.accept_15_2_11_5_1_1266 62 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 215 (accept_3_2 61 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 215
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 215 (accept_3_2 58 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 57 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 56 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 215 (accept_3_2 55 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 215 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 215
  (Polychromatic418967fa.accept_15_8_11_5_1_169 53 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 215 (accept_3_2 52 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 51 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 215 (Polychromatic418967fa.accept_13_11_1_7_1_1691 50 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 215 (accept_3_2 49 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 48 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 47 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 215 (accept_3_2 46 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 215 (Polychromatic418967fa.accept_13_6_1_7_1_1690 45 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 44 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 215 (accept_3_2 43 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 42 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 215
  (Polychromatic418967fa.accept_16_9_3_7_1_6883 41 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 215 (accept_3_2 40 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 39 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 38 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 215 (accept_3_2 37 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 215
  (Polychromatic418967fa.accept_22_13_21_17_1_12690 35 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 131 215 (accept_3_2 34 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 33 131 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 215 (Polychromatic418967fa.accept_13_6_1_7_1_1690 32 131
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 215 (accept_3_2 31 131
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 215
  (Polychromatic418967fa.accept_9_3_5_8_1_99 30 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 131 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 131 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 215 (accept_3_2 28 131 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 131 215 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 215
  (Polychromatic418967fa.accept_10_6_1_5_1_1024 26 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 215 (accept_3_2 25 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 24 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 215 (Polychromatic418967fa.accept_15_8_11_5_1_169 23 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 215 (accept_3_2 22 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 21 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 215
  (Polychromatic418967fa.accept_8_4_3_7_1_491 20 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 215 (accept_3_2 19 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 215 (Polychromatic418967fa.accept_19_18_17_6_1_5775 18 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 215 (Polychromatic418967fa.accept_15_2_11_5_1_1266 17 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 215 (accept_3_2 16 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 131 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 215
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 131 215 (accept_3_2 13 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 131 215 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 131 215 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 215 (accept_3_2 10 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 215 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 215
  (Polychromatic418967fa.accept_13_8_1_7_1_2505 8 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 215 (accept_3_2 7 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 215 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 215 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 215 (accept_3_2 4 131 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 215 (Polychromatic418967fa.accept_9_3_5_8_1_99 3 131 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 215
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 215 (accept_3_2 1 131 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 130 215
  (Eq.refl Bool.true) (allA_of_3_0 86 130 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 129 215 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 129 215 43 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 129 215 (accept_3_2 85 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 129 215 (Polychromatic418967fa.accept_10_4_9_5_1_84 84 129 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 83 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 215 (accept_3_2 82 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 215 (Polychromatic418967fa.accept_10_1_9_5_1_83
  81 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 80 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 215 (accept_3_2 79 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 77 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 215 (accept_3_2 76 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 75 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 215 (accept_3_2 73 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 72 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 71 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 215 (accept_3_2 70 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 69 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 68 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 215 (accept_3_2 67 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 65 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 215 (accept_3_2 64 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 63 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 215 (accept_3_2 61 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 60 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 59 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 215 (accept_3_2 58 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 57 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 56 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 129 215 (accept_3_2 55 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 129 215 (Polychromatic418967fa.accept_25_3_4_15_1_12689 53 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 215 (accept_3_2 52 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 51 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 215 (accept_3_2 49 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 215 (Polychromatic418967fa.accept_15_3_9_5_1_2082 48 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 47 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 215 (accept_3_2 46 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 215 (Polychromatic418967fa.accept_13_6_12_7_1_5131 45 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 44 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 43 129 215 43 1 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 42 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 129 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 41 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 215 (accept_3_2 40 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 215 (Polychromatic418967fa.accept_12_3_9_11_1_231
  39 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 215 (accept_3_2 37 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 36 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 215 (Polychromatic418967fa.accept_17_1_10_11_1_2943 35 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 215 (accept_3_2 34 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 32 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 215 (accept_3_2 31 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 29 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 215 (accept_3_2 28 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 215 (Polychromatic418967fa.accept_12_3_9_11_1_231 27 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 215 (accept_3_2 25 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 215 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 23 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 215 (accept_3_2 22 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 215 (Polychromatic418967fa.accept_10_1_9_5_1_83 21 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 20 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 215 (accept_3_2 19 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 215 (Polychromatic418967fa.accept_13_4_12_7_1_2439 17 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 215 (accept_3_2 16 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 215 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 129 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 215 (accept_3_2 13 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 215 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 215 (Polychromatic418967fa.accept_9_2_3_8_1_318 11 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 215 (accept_3_2 10 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 215 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 215
  (Polychromatic418967fa.accept_6_2_3_5_1_26 8 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 215 (accept_3_2 7 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 215 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 215 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 215 (accept_3_2 4 129 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 215 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 129 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 215
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 215 (accept_3_2 1 129 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 128 215
  (Eq.refl Bool.true) (allA_succ_of_accept 87 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 87 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 128 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 86 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 128 215 (accept_3_2 85 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 128 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 84 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 128 215 (Polychromatic418967fa.accept_10_3_8_5_1_606 83 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 128 215 (accept_3_2 82 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 81 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 128 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 80 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 128 215 (accept_3_2 79 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 128 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 78 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 128 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 77 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 128 215 (accept_3_2 76 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 75 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 128 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 74 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 128 215 (accept_3_2 73 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 128 215 (Polychromatic418967fa.accept_10_2_8_5_1_587 72 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 128 215 (Polychromatic418967fa.accept_15_11_8_5_1_1278 71 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 128 215 (accept_3_2 70 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 69 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 128 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 68 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 128 215 (accept_3_2 67 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 66 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 215 (Polychromatic418967fa.accept_18_11_2_17_1_3490 65 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 215 (accept_3_2 64 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 63 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 215
  (Polychromatic418967fa.accept_10_2_8_5_1_587 62 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 215 (accept_3_2 61 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 60 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 59 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 215 (accept_3_2 58 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 57 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 215
  (Polychromatic418967fa.accept_11_1_7_6_1_378 56 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 128 215 (accept_3_2 55 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 128 215 (Polychromatic418967fa.accept_17_3_9_11_1_11600 54 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 128 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 53 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 215 (accept_3_2 52 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 51 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 128 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 50 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 128 215 (accept_3_2 49 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 128 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 48 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 128 215 (Polychromatic418967fa.accept_10_7_8_5_1_1008 47 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 215 (accept_3_2 46 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 45 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 128 215
  (Polychromatic418967fa.accept_13_5_11_7_1_559 44 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 128 215 (accept_3_2 43 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 128 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 42 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 128 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 215 (accept_3_2 40 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 39 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 215
  (Polychromatic418967fa.accept_7_3_2_5_1_147 38 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 128 215 (accept_3_2 37 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 128 215 (Polychromatic418967fa.accept_17_2_9_11_1_4057 36 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 128 215 (Polychromatic418967fa.accept_13_9_11_7_1_1077 35 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 215 (accept_3_2 34 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 33 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 215
  (Polychromatic418967fa.accept_7_4_2_5_1_527 32 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 215 (accept_3_2 31 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 30 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 215 (Polychromatic418967fa.accept_13_3_11_7_1_2488 29 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 215 (accept_3_2 28 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 27 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 215
  (Polychromatic418967fa.accept_12_2_8_11_1_31 26 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 215 (accept_3_2 25 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 24 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 215 (accept_3_2 22 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 21 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 215
  (Polychromatic418967fa.accept_17_3_9_11_1_11600 20 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 128 215 (accept_3_2 19 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 128 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 18 128 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 215 (Polychromatic418967fa.accept_7_3_2_5_1_147 17 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 215 (accept_3_2 16 128 215
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 15
  128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 215
  (Polychromatic418967fa.accept_9_5_2_8_1_109 14 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 215 (accept_3_2 13 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 215 (Polychromatic418967fa.accept_9_3_2_8_1_108 12 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 215 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 215 (accept_3_2 10 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 9 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 215
  (Polychromatic418967fa.accept_17_8_9_11_1_3976 8 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 215 (accept_3_2 7 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 215 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 215 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 215 (accept_3_2 4 128 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 215 (Polychromatic418967fa.accept_6_3_2_5_1_32 3 128 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 215
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 215 (accept_3_2 1 128 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  215)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 127 215
  (Eq.refl Bool.true) (allA_of_3_0 89 127 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 126 215 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 126 215 (accept_3_2 88 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 126 215 (Polychromatic418967fa.accept_11_10_5_6_1_1842 87 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 126 215
  (Polychromatic418967fa.accept_13_8_9_7_1_530 86 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 126 215 (accept_3_2 85 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 126 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 84 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 126 215 (Polychromatic418967fa.accept_25_8_1_15_1_12688 83 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 126 215 (accept_3_2 82 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 126 215
  (Polychromatic418967fa.accept_13_2_9_7_1_164 80 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 126 215 (accept_3_2 79 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 126 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 78 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 126 215 (accept_3_2 76 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 126 215 (Polychromatic418967fa.accept_19_18_12_6_1_7187 75 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 126 215
  (Polychromatic418967fa.accept_10_4_6_5_1_74 74 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 126 215 (accept_3_2 73 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 126 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 72 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 126 215 (Polychromatic418967fa.accept_10_1_6_5_1_304 71 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 126 215 (accept_3_2 70 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 126 215
  (Polychromatic418967fa.accept_13_3_9_7_1_1730 68 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 126 215 (accept_3_2 67 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 126 215 (Polychromatic418967fa.accept_23_20_11_8_1_7798 66 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 215 (accept_3_2 64 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 126 215 (Polychromatic418967fa.accept_13_11_9_7_1_2484 63 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 126 215
  (Polychromatic418967fa.accept_22_18_16_17_1_8011 62 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 126 215 (accept_3_2 61 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 126 215 (Polychromatic418967fa.accept_13_8_9_7_1_530 60 126 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 126 215 (Polychromatic418967fa.accept_10_9_6_5_1_1002 59 126
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 215 (accept_3_2 58 126
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9
  57 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 126 215
  (Polychromatic418967fa.accept_11_1_5_6_1_397 56 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 126 215 (accept_3_2 55 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 126 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 54 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 215 (accept_3_2 52 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 126 215 (Polychromatic418967fa.accept_10_1_6_5_1_304 51 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 126 215
  (Polychromatic418967fa.accept_13_11_9_7_1_2484 50 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 215 (accept_3_2 49 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 126 215 (Polychromatic418967fa.accept_15_3_6_5_1_2079 48 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 126 215 (Polychromatic418967fa.accept_13_8_9_7_1_530 47 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 215 (accept_3_2 46 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 126 215
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 215 (accept_3_2 43 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 126 215 (Polychromatic418967fa.accept_13_3_9_7_1_1730 42 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 215 (accept_3_2 40 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 126 215 (Polychromatic418967fa.accept_10_9_6_5_1_1002 39 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 126 215
  (Polychromatic418967fa.accept_27_11_18_26_1_12687 38 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 126 215 (accept_3_2 37 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 126 215 (Polychromatic418967fa.accept_16_4_14_7_1_5641 36 126 215 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 126 215 (Polychromatic418967fa.accept_17_1_7_11_1_2892 35 126
  215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 215 (accept_3_2 34 126
  215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9
  33 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 126 215
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 32 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 215 (accept_3_2 31 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 126 215 (Polychromatic418967fa.accept_13_4_9_7_1_2402 30 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 215 (accept_3_2 28 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 126 215 (Polychromatic418967fa.accept_15_12_6_5_1_1275 27 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 126 215
  (Polychromatic418967fa.accept_15_11_6_5_1_1295 26 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 126 215 (accept_3_2 25 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 126 215 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 126 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 23 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 126 215 (accept_3_2 22 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 126 215
  (Polychromatic418967fa.accept_16_4_14_7_1_5641 20 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 126 215 (accept_3_2 19 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 126 215 (Polychromatic418967fa.accept_15_3_6_5_1_2079 18 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 215 (accept_3_2 16 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 126 215 (Polychromatic418967fa.accept_13_2_9_7_1_164 15 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 126 215
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 215 (accept_3_2 13 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 126 215 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 126 215 (Polychromatic418967fa.accept_10_1_6_5_1_304 11 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 215 (accept_3_2 10 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 126 215
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 126 215
  (Polychromatic418967fa.accept_13_8_9_7_1_530 8 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 126 215 (accept_3_2 7 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  126 215 (Polychromatic418967fa.accept_13_6_9_7_1_2430 6 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 126 215 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 126 215 (accept_3_2 4 126 215 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 126 215 (Polychromatic418967fa.accept_13_3_9_7_1_1730 3 126 215 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 126 215
  (Polychromatic418967fa.accept_13_2_9_7_1_164 2 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 126 215 (accept_3_2 1 126 215 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  215))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_215_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


